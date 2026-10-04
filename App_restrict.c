#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <time.h>
#include <poll.h>
#include <signal.h>
#include <dirent.h>
#include <ctype.h>
#include <stdbool.h>
#include <sys/epoll.h>
#include <sys/inotify.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <linux/input.h>
#include <linux/limits.h>

/* ===== 全局参数 ===== */
static char g_log_path[PATH_MAX] = "/data/adb/modules/App_screen_off/app_screen_off.log";
static char g_config_path[PATH_MAX] = "/data/adb/modules/App_screen_off/config.prop";
static bool g_debug = false;
static int g_cmd_timeout_ms = 80;
static int g_front_cache_sec = 3;
static int g_screen_check_sec = 10;
static int g_max_poll_interval = 10;
static int g_check_sec = 10;

#define MAX_LOG_SIZE (100 * 1024)
#define LOG_I(fmt, ...) do_log("I", fmt, ##__VA_ARGS__)
#define LOG_W(fmt, ...) do_log("W", fmt, ##__VA_ARGS__)
#define LOG_E(fmt, ...) do_log("E", fmt, ##__VA_ARGS__)
#define LOG_D(fmt, ...) do { if (g_debug) do_log("D", fmt, ##__VA_ARGS__); } while(0)

void do_log(const char *level, const char *fmt, ...) {
    FILE *f = fopen(g_log_path, "a");
    if (!f) return;
    time_t now = time(NULL);
    struct tm *tm = localtime(&now);
    char ts[32];
    strftime(ts, sizeof(ts), "%Y-%m-%d %H:%M:%S", tm);
    fprintf(f, "[%s][%s] ", ts, level);
    va_list args;
    va_start(args, fmt);
    vfprintf(f, fmt, args);
    va_end(args);
    fprintf(f, "\n");
    fclose(f);
}

void rotate_log_if_needed(void) {
    struct stat st;
    if (stat(g_log_path, &st) == 0 && st.st_size > MAX_LOG_SIZE) {
        char old[PATH_MAX];
        snprintf(old, sizeof(old), "%s.old", g_log_path);
        rename(g_log_path, old);
    }
}

/* ===== 应用配置 ===== */
#define MAX_APPS 32
typedef struct {
    char package[128];
    long limit_time_sec;
    long start_time;
    long last_touch_time;
    int bg_mismatch_count;
} AppConfig;

static AppConfig apps[MAX_APPS];
static int app_count = 0;

static char cached_top_app[128] = {0};
static long cache_expire_time = 0;
static long last_real_touch_time = 0;

static int prev_screen_state = -1;  // -1=未知, 0=熄, 1=亮

#define MAX_TOUCH_DEVS 16
static int touch_fds[MAX_TOUCH_DEVS];
static int touch_fd_count = 0;

/* ===== 命令行参数解析 ===== */
static void parse_args(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "--config=", 9) == 0) {
            strncpy(g_config_path, argv[i] + 9, PATH_MAX - 1);
        } else if (strncmp(argv[i], "--log=", 6) == 0) {
            strncpy(g_log_path, argv[i] + 6, PATH_MAX - 1);
        } else if (strcmp(argv[i], "--debug=true") == 0 || strcmp(argv[i], "--debug=1") == 0) {
            g_debug = true;
        }
    }
}

/* ===== 配置解析 ===== */
static void load_config(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) {
        LOG_W("配置文件不存在: %s", path);
        return;
    }

    char line[512];
    int line_num = 0;
    AppConfig *current = NULL;
    app_count = 0;

    while (fgets(line, sizeof(line), f)) {
        line_num++;
        size_t len = strlen(line);
        while (len > 0 && (line[len-1] == '\n' || line[len-1] == '\r' ||
               line[len-1] == ' ' || line[len-1] == '\t')) {
            line[--len] = '\0';
        }
        if (len == 0 || line[0] == '#') continue;

        char *eq = strchr(line, '=');
        if (!eq) continue;
        *eq = '\0';
        char *key = line;
        char *value = eq + 1;

        while (*key == ' ' || *key == '\t') key++;
        char *kend = key + strlen(key) - 1;
        while (kend > key && (*kend == ' ' || *kend == '\t')) { *kend = '\0'; kend--; }

        while (*value == ' ' || *value == '\t') value++;
        char *vend = value + strlen(value) - 1;
        while (vend > value && (*vend == ' ' || *vend == '\t' ||
               *vend == '\r' || *vend == '\n')) { *vend = '\0'; vend--; }

        if (strcmp(key, "cmd_timeout_ms") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 50 && v <= 5000) g_cmd_timeout_ms = (int)v;
        } else if (strcmp(key, "front_cache_sec") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 1 && v <= 3600) g_front_cache_sec = (int)v;
        } else if (strcmp(key, "screen_check_sec") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 1 && v <= 300) g_screen_check_sec = (int)v;
        } else if (strcmp(key, "max_poll_interval") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 1 && v <= 60) g_max_poll_interval = (int)v;
        } else if (strcmp(key, "check_sec") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 1 && v <= 120) g_check_sec = (int)v;
        } else if (strcmp(key, "limit_time") == 0) {
            if (!current) {
                LOG_W("配置行%d: limit_time出现在package之前，已忽略", line_num);
                continue;
            }
            long val = 0;
            char *endp;
            val = strtol(value, &endp, 10);
            if (endp == value) continue;
            char suffix = *endp;
            if (suffix == 's' || suffix == '\0') {
                current->limit_time_sec = val;
            } else if (suffix == 'm') {
                current->limit_time_sec = val * 60;
            } else if (suffix == 'h') {
                current->limit_time_sec = val * 3600;
            } else {
                current->limit_time_sec = val;
            }
            LOG_I("配置更新: limit_time=%ld秒 (应用=%s)",
                  current->limit_time_sec, current->package);
        } else if (strcmp(key, "package") == 0) {
            if (app_count >= MAX_APPS) continue;
            current = &apps[app_count++];
            strncpy(current->package, value, sizeof(current->package) - 1);
            current->package[sizeof(current->package) - 1] = '\0';
            current->limit_time_sec = 0;
            current->start_time = 0;
            current->last_touch_time = 0;
            current->bg_mismatch_count = 0;
            LOG_I("应用配置[%d]: package=%s", app_count - 1, current->package);
        }
    }
    fclose(f);
    LOG_I("========== 配置加载完成，共%d个应用 ==========", app_count);
    for (int i = 0; i < app_count; i++) {
        LOG_I("  [%d] package=%s, limit_time=%ld秒", i, apps[i].package, apps[i].limit_time_sec);
    }
}

/* ===== 前台应用检测 ===== */
static bool get_top_app_name(char *out, size_t out_size) {
    long now = time(NULL);
    if (cache_expire_time > now && cached_top_app[0] != '\0') {
        strncpy(out, cached_top_app, out_size - 1);
        return true;
    }

    char cmd[256];
    snprintf(cmd, sizeof(cmd), "dumpsys window | grep -E 'mCurrentFocus|mFocusedApp' | head -1");
    char result[512] = {0};

    int pipefd[2];
    if (pipe(pipefd) != 0) return false;
    pid_t pid = fork();
    if (pid < 0) { close(pipefd[0]); close(pipefd[1]); return false; }
    if (pid == 0) {
        close(pipefd[0]);
        dup2(pipefd[1], STDOUT_FILENO);
        dup2(pipefd[1], STDERR_FILENO);
        close(pipefd[1]);
        execl("/system/bin/sh", "sh", "-c", cmd, NULL);
        _exit(127);
    }
    close(pipefd[1]);
    int flags = fcntl(pipefd[0], F_GETFL, 0);
    fcntl(pipefd[0], F_SETFL, flags | O_NONBLOCK);

    struct pollfd pfd = { .fd = pipefd[0], .events = POLLIN };
    long deadline = clock_gettime_mono_ms() + g_cmd_timeout_ms;
    int got_data = 0;
    while (clock_gettime_mono_ms() < deadline) {
        int remaining = deadline - clock_gettime_mono_ms();
        int ret = poll(&pfd, 1, remaining);
        if (ret > 0 && (pfd.revents & POLLIN)) {
            ssize_t n = read(pipefd[0], result, sizeof(result) - 1);
            if (n > 0) { got_data = 1; break; }
        } else if (ret == 0) break;
    }
    int status;
    waitpid(pid, &status, WNOHANG);
    close(pipefd[0]);

    if (!got_data) return false;

    char *pkg_start = strstr(result, "u0 ");
    if (pkg_start) {
        pkg_start += 3;
        char *pkg_end = strchr(pkg_start, '/');
        if (pkg_end) {
            size_t pkg_len = pkg_end - pkg_start;
            if (pkg_len < out_size) {
                strncpy(out, pkg_start, pkg_len);
                out[pkg_len] = '\0';
                strncpy(cached_top_app, out, sizeof(cached_top_app) - 1);
                cache_expire_time = now + g_front_cache_sec;
                return true;
            }
        }
    }
    return false;
}

static long clock_gettime_mono_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* ===== 触摸设备发现 ===== */
static void find_touch_devices(void) {
    DIR *dir = opendir("/dev/input");
    if (!dir) return;
    struct dirent *ent;
    while ((ent = readdir(dir)) && touch_fd_count < MAX_TOUCH_DEVS) {
        if (strncmp(ent->d_name, "event", 5) != 0) continue;
        char path[PATH_MAX];
        snprintf(path, sizeof(path), "/dev/input/%s", ent->d_name);
        int fd = open(path, O_RDONLY | O_NONBLOCK);
        if (fd < 0) continue;

        unsigned long evbit[EV_MAX / (sizeof(unsigned long) * 8) + 1] = {0};
        if (ioctl(fd, EVIOCGBIT(0, sizeof(evbit)), evbit) < 0) { close(fd); continue; }

        unsigned long absbit[ABS_MAX / (sizeof(unsigned long) * 8) + 1] = {0};
        bool has_abs = false;
        if (evbit[EV_ABS / (sizeof(unsigned long) * 8)] & (1UL << (EV_ABS % (sizeof(unsigned long) * 8)))) {
            has_abs = true;
        }
        unsigned long keybit[KEY_MAX / (sizeof(unsigned long) * 8) + 1] = {0};
        bool has_btn = false;
        if (evbit[EV_KEY / (sizeof(unsigned long) * 8)] & (1UL << (EV_KEY % (sizeof(unsigned long) * 8)))) {
            if (ioctl(fd, EVIOCGBIT(EV_KEY, sizeof(keybit)), keybit) >= 0) {
                has_btn = (keybit[BTN_TOUCH / (sizeof(unsigned long) * 8)] &
                           (1UL << (BTN_TOUCH % (sizeof(unsigned long) * 8)))) != 0;
            }
        }

        if (has_abs || has_btn) {
            touch_fds[touch_fd_count++] = fd;
            LOG_I("发现输入设备: %s (fd=%d)", path, fd);
        } else {
            close(fd);
        }
    }
    closedir(dir);
}

/* ===== 触摸检测 ===== */
static bool check_touch_input(void) {
    bool touch_detected = false;
    long now = time(NULL);
    for (int i = 0; i < touch_fd_count; i++) {
        int fd = touch_fds[i];
        struct input_event ev;
        while (read(fd, &ev, sizeof(ev)) > 0) {
            bool is_touch = false;
            if (ev.type == EV_ABS && (
                ev.code == ABS_MT_POSITION_X || ev.code == ABS_MT_POSITION_Y ||
                ev.code == ABS_MT_TRACKING_ID || ev.code == ABS_MT_PRESSURE ||
                ev.code == ABS_X || ev.code == ABS_Y)) {
                is_touch = true;
            } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH && ev.value == 1) {
                is_touch = true;
            }
            if (is_touch) {
                touch_detected = true;
                last_real_touch_time = now;
            }
        }
    }
    return touch_detected;
}

/* ===== 屏幕状态 ===== */
static int read_screen_state(void) {
    const char *paths[] = {
        "/sys/class/backlight/panel/brightness",
        "/sys/class/leds/lcd-backlight/brightness",
        "/sys/class/backlight/backlight/brightness",
        NULL
    };
    for (int i = 0; paths[i]; i++) {
        FILE *f = fopen(paths[i], "r");
        if (f) {
            int val;
            if (fscanf(f, "%d", &val) == 1) { fclose(f); return val > 0 ? 1 : 0; }
            fclose(f);
        }
    }
    return -1;  // sysfs不可用
}

static void handle_screen_state_change(int new_state) {
    if (prev_screen_state == -1) {
        prev_screen_state = new_state;
        return;
    }
    if (prev_screen_state == 1 && new_state == 0) {
        LOG_I("屏幕状态: 亮 -> 熄，重置所有应用跟踪状态");
        for (int i = 0; i < app_count; i++) {
            apps[i].start_time = 0;
            apps[i].last_touch_time = 0;
            apps[i].bg_mismatch_count = 0;
        }
        cached_top_app[0] = '\0';
        cache_expire_time = 0;
    } else if (prev_screen_state == 0 && new_state == 1) {
        LOG_I("屏幕状态: 熄 -> 亮，清除缓存重新检测");
        cached_top_app[0] = '\0';
        cache_expire_time = 0;
        for (int i = 0; i < app_count; i++) {
            apps[i].start_time = 0;
            apps[i].last_touch_time = 0;
            apps[i].bg_mismatch_count = 0;
        }
    }
    prev_screen_state = new_state;
}

static void trigger_screen_off(void) {
    LOG_I("触发屏幕息屏");
    system("input keyevent KEYCODE_POWER");
}

/* ===== 主循环 ===== */
static bool g_running = true;
static void sig_handler(int sig) { (void)sig; g_running = false; }

int main(int argc, char **argv) {
    parse_args(argc, argv);

    signal(SIGTERM, sig_handler);
    signal(SIGINT, sig_handler);
    setpriority(PRIO_PROCESS, 0, 19);

    rotate_log_if_needed();
    LOG_I("========================================");
    LOG_I("  App_screen_off 守护进程启动");
    LOG_I("  配置文件: %s", g_config_path);
    LOG_I("  日志文件: %s", g_log_path);
    LOG_I("  调试模式: %s", g_debug ? "开启" : "关闭");
    LOG_I("========================================");

    load_config(g_config_path);
    if (app_count == 0) {
        LOG_E("没有配置任何应用，退出");
        return 1;
    }

    find_touch_devices();
    if (touch_fd_count == 0) LOG_W("未发现触摸设备");

    int inotify_fd = inotify_init1(IN_NONBLOCK);
    int wd = inotify_add_watch(inotify_fd, g_config_path, IN_MODIFY);
    (void)wd;

    int epoll_fd = epoll_create1(0);
    struct epoll_event ev;
    ev.events = EPOLLIN;
    ev.data.fd = inotify_fd;
    epoll_ctl(epoll_fd, EPOLL_CTL_ADD, inotify_fd, &ev);
    for (int i = 0; i < touch_fd_count; i++) {
        ev.events = EPOLLIN | EPOLLET;
        ev.data.fd = touch_fds[i];
        epoll_ctl(epoll_fd, EPOLL_CTL_ADD, touch_fds[i], &ev);
    }

    long last_screen_check = 0;
    long last_app_check = 0;
    char last_seen_app[128] = {0};

    LOG_I("进入主循环...");

    while (g_running) {
        long now_sec = time(NULL);

        // 动态epoll超时
        int timeout_ms = g_max_poll_interval * 1000;
        bool is_tracking = false;
        for (int i = 0; i < app_count; i++) {
            if (apps[i].start_time != 0 && apps[i].last_touch_time != 0) {
                is_tracking = true;
                long elapsed = now_sec - apps[i].last_touch_time;
                long remaining = apps[i].limit_time_sec - elapsed;
                if (remaining > 0 && remaining * 1000 < timeout_ms) {
                    timeout_ms = (int)(remaining * 1000);
                }
                if (remaining <= 0) timeout_ms = 0;
            }
        }

        struct epoll_event events[32];
        int nfds = epoll_wait(epoll_fd, events, 32, timeout_ms);
        if (nfds > 0) {
            for (int i = 0; i < nfds; i++) {
                if (events[i].data.fd == inotify_fd) {
                    struct inotify_event ie;
                    if (read(inotify_fd, &ie, sizeof(ie)) > 0) {
                        if (ie.mask & IN_MODIFY) {
                            LOG_I("配置文件修改，重新加载");
                            load_config(g_config_path);
                        }
                    }
                } else {
                    check_touch_input();
                }
            }
        }

        now_sec = time(NULL);

        // 屏幕状态边沿检测
        if (now_sec - last_screen_check >= g_screen_check_sec) {
            last_screen_check = now_sec;
            int screen_state = read_screen_state();
            if (screen_state != -1) {
                handle_screen_state_change(screen_state);
            }
            if (screen_state == 0) continue;
        }

        // 前台检测节流
        if (now_sec - last_app_check >= g_check_sec) {
            last_app_check = now_sec;

            char current_app[128] = {0};
            if (get_top_app_name(current_app, sizeof(current_app))) {
                if (strcmp(current_app, last_seen_app) != 0) {
                    LOG_I("前台应用变更: %s -> %s",
                          last_seen_app[0] ? last_seen_app : "(无)", current_app);
                    strncpy(last_seen_app, current_app, sizeof(last_seen_app) - 1);
                }

                for (int i = 0; i < app_count; i++) {
                    AppConfig *app = &apps[i];
                    if (strcmp(current_app, app->package) == 0) {
                        app->bg_mismatch_count = 0;
                        if (app->start_time == 0) {
                            app->start_time = now_sec;
                            app->last_touch_time = now_sec;
                            LOG_I("开始跟踪: %s (超时=%ld秒)", app->package, app->limit_time_sec);
                        }
                        if (check_touch_input()) {
                            app->last_touch_time = now_sec;
                        }
                        long elapsed = now_sec - app->last_touch_time;
                        if (elapsed >= app->limit_time_sec) {
                            LOG_I("无触摸超时，触发息屏 (应用=%s, 已无操作%ld秒)",
                                  app->package, elapsed);
                            trigger_screen_off();
                            app->start_time = 0;
                            app->last_touch_time = 0;
                        }
                    } else {
                        if (app->start_time != 0) {
                            app->bg_mismatch_count++;
                            if (app->bg_mismatch_count >= 5) {
                                LOG_I("应用切后台，停止跟踪: %s", app->package);
                                app->start_time = 0;
                                app->last_touch_time = 0;
                                app->bg_mismatch_count = 0;
                            }
                        }
                    }
                }
            }
        }
        usleep(10000);
    }

    LOG_I("守护进程退出");
    close(epoll_fd);
    close(inotify_fd);
    for (int i = 0; i < touch_fd_count; i++) close(touch_fds[i]);
    return 0;
}
