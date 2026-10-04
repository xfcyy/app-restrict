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

/* ===== 日志 ===== */
#define LOG_FILE "/data/adb/modules/App_screen_off_Aloazny/app_screen_off.log"
#define MAX_LOG_SIZE (100 * 1024)

#define LOG_I(fmt, ...) do_log("I", fmt, ##__VA_ARGS__)
#define LOG_W(fmt, ...) do_log("W", fmt, ##__VA_ARGS__)
#define LOG_E(fmt, ...) do_log("E", fmt, ##__VA_ARGS__)

void do_log(const char *level, const char *fmt, ...) {
    FILE *f = fopen(LOG_FILE, "a");
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
    if (stat(LOG_FILE, &st) == 0 && st.st_size > MAX_LOG_SIZE) {
        char old[PATH_MAX];
        snprintf(old, sizeof(old), "%s.old", LOG_FILE);
        rename(LOG_FILE, old);
    }
}

/* ===== 全局配置 ===== */
static int g_cmd_timeout_ms = 80;        /* 【优化】从150降到80，dumpsys正常30~50ms返回 */
static int g_front_cache_sec = 3;        /* 前台应用名缓存时间 */
static int g_check_sec = 10;             /* 【优化】屏幕状态+前台检测周期，用户可改 */
static int g_max_poll_interval = 10;     /* epoll最大超时 */

/* ===== 应用配置 ===== */
#define MAX_APPS 32
#define BG_MISMATCH_THRESHOLD 5

typedef struct {
    char package[128];
    long limit_time_sec;
    long start_time;
    long last_touch_time;
    int bg_mismatch_count;
} AppConfig;

static AppConfig apps[MAX_APPS];
static int app_count = 0;

/* ===== 状态 ===== */
static char cached_top_app[128] = {0};
static long cache_expire_time = 0;
static long last_real_touch_time = 0;    /* 最后一次检测到触摸的时间戳 */
static int prev_screen_state = -1;       /* 上次屏幕状态：1=亮，0=熄，-1=未知 */

/* ===== 函数声明 ===== */
static void load_config(const char *path);
static bool get_top_app_name(char *out, size_t out_size);
static FILE* popen_timeout(const char *cmd, int timeout_ms);
static long get_time_ms(void);
static void find_touch_devices(void);
static bool check_touch_input(void);
static int get_screen_state(void);       /* 返回值：1=亮，0=熄，-1=不可用 */
static void trigger_screen_off(void);

/* ===== 触摸设备 ===== */
#define MAX_TOUCH_DEVS 16
static int touch_fds[MAX_TOUCH_DEVS];
static int touch_fd_count = 0;

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
        /* 去尾部\r\n和首尾空白 */
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

        /* 去key首尾空白 */
        while (*key == ' ' || *key == '\t') key++;
        char *kend = key + strlen(key) - 1;
        while (kend > key && (*kend == ' ' || *kend == '\t')) { *kend = '\0'; kend--; }

        /* 去value首尾空白（含\r，修复CRLF污染） */
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
        } else if (strcmp(key, "check_sec") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 1 && v <= 120) g_check_sec = (int)v;
        } else if (strcmp(key, "max_poll_interval") == 0) {
            long v = strtol(value, NULL, 10);
            if (v >= 1 && v <= 60) g_max_poll_interval = (int)v;
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
                if (suffix == '\0') LOG_I("注意: limit_time=%ld 无后缀，按秒解释", val);
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

/* ===== 前台应用检测（优化：单次尝试，失败即返回，无备用路径）===== */
static bool get_top_app_name(char *out, size_t out_size) {
    long now = time(NULL);
    if (cache_expire_time > now && cached_top_app[0] != '\0') {
        strncpy(out, cached_top_app, out_size - 1);
        return true;
    }

    char cmd[256];
    snprintf(cmd, sizeof(cmd), "dumpsys window | grep -E 'mCurrentFocus|mFocusedApp' | head -1");

    char result[512] = {0};
    FILE *fp = popen_timeout(cmd, g_cmd_timeout_ms);
    if (fp) {
        fgets(result, sizeof(result), fp);
        pclose(fp);
    }

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

/* ===== 带超时的popen（优化：超时内不打印警告，减少日志噪音）===== */
static FILE* popen_timeout(const char *cmd, int timeout_ms) {
    int pipefd[2];
    if (pipe(pipefd) != 0) return NULL;

    pid_t pid = fork();
    if (pid < 0) {
        close(pipefd[0]); close(pipefd[1]);
        return NULL;
    }

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
    long deadline = get_time_ms() + timeout_ms;
    FILE *result_fp = NULL;

    while (get_time_ms() < deadline) {
        int remaining = deadline - get_time_ms();
        int ret = poll(&pfd, 1, remaining);
        if (ret > 0 && (pfd.revents & POLLIN)) {
            result_fp = fdopen(pipefd[0], "r");
            break;
        } else if (ret == 0) {
            break;  /* 超时，静默放弃 */
        }
    }

    if (!result_fp) {
        kill(pid, SIGKILL);
        waitpid(pid, NULL, WNOHANG);
        close(pipefd[0]);
    }
    return result_fp;
}

static long get_time_ms(void) {
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
        if (ioctl(fd, EVIOCGBIT(0, sizeof(evbit)), evbit) < 0) {
            close(fd); continue;
        }

        unsigned long absbit[ABS_MAX / (sizeof(unsigned long) * 8) + 1] = {0};
        bool has_abs = false;
        if (evbit[EV_ABS / (sizeof(unsigned long) * 8)] &
            (1UL << (EV_ABS % (sizeof(unsigned long) * 8)))) {
            has_abs = true;
        }

        unsigned long keybit[KEY_MAX / (sizeof(unsigned long) * 8) + 1] = {0};
        bool has_btn = false;
        if (evbit[EV_KEY / (sizeof(unsigned long) * 8)] &
            (1UL << (EV_KEY % (sizeof(unsigned long) * 8)))) {
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

/* ===== 触摸检测（修复：SYN_REPORT不再算触摸）===== */
static bool check_touch_input(void) {
    bool touch_detected = false;
    long now = time(NULL);

    for (int i = 0; i < touch_fd_count; i++) {
        int fd = touch_fds[i];
        struct input_event ev;
        while (read(fd, &ev, sizeof(ev)) > 0) {
            bool is_touch = false;

            /* 只认真正的触摸事件 */
            if (ev.type == EV_ABS && (
                ev.code == ABS_MT_POSITION_X ||
                ev.code == ABS_MT_POSITION_Y ||
                ev.code == ABS_MT_TRACKING_ID ||
                ev.code == ABS_MT_PRESSURE ||
                ev.code == ABS_X ||
                ev.code == ABS_Y)) {
                is_touch = true;
            } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH && ev.value == 1) {
                is_touch = true;
            }
            /* SYN_REPORT 不再算触摸，彻底解决空闲期误触发 */

            if (is_touch) {
                touch_detected = true;
                last_real_touch_time = now;
            }
        }
    }
    return touch_detected;
}

/* ===== 屏幕状态检测（优化：返回-1表示sysfs不可用）===== */
static int get_screen_state(void) {
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
            if (fscanf(f, "%d", &val) == 1) {
                int result = val > 0 ? 1 : 0;
                fclose(f);
                return result;
            }
            fclose(f);
        }
    }
    return -1;  /* sysfs不可用 */
}

static void trigger_screen_off(void) {
    LOG_I("触发屏幕息屏");
    system("input keyevent KEYCODE_POWER");
}

/* ===== 主循环 ===== */
static bool g_running = true;

static void sig_handler(int sig) {
    (void)sig;
    g_running = false;
}

int main(void) {
    signal(SIGTERM, sig_handler);
    signal(SIGINT, sig_handler);
    setpriority(PRIO_PROCESS, 0, 19);

    rotate_log_if_needed();
    LOG_I("========================================");
    LOG_I("  App_screen_off 守护进程启动");
    LOG_I("========================================");

    const char *config_path = "/data/adb/modules/App_screen_off/config.prop";
    load_config(config_path);

    if (app_count == 0) {
        LOG_E("没有配置任何应用，退出");
        return 1;
    }

    find_touch_devices();
    if (touch_fd_count == 0) {
        LOG_W("未发现触摸设备");
    }

    int inotify_fd = inotify_init1(IN_NONBLOCK);
    int wd = inotify_add_watch(inotify_fd, config_path, IN_MODIFY);
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

    long last_check_sec = 0;
    char last_seen_app[128] = {0};

    LOG_I("进入主循环...");

    while (g_running) {
        long now_sec = time(NULL);

        /* 【优化】动态计算epoll超时：根据正在跟踪的应用剩余时间缩短等待 */
        int timeout_ms = g_max_poll_interval * 1000;
        for (int i = 0; i < app_count; i++) {
            if (apps[i].start_time != 0 && apps[i].last_touch_time != 0) {
                long elapsed = now_sec - apps[i].last_touch_time;
                long remaining = apps[i].limit_time_sec - elapsed;
                if (remaining <= 0) {
                    timeout_ms = 0;  /* 已超时，立即wake */
                } else if (remaining * 1000 < timeout_ms) {
                    timeout_ms = remaining * 1000;
                }
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
                            load_config(config_path);
                        }
                    }
                } else {
                    /* 触摸事件到达 - 消费事件并立即更新计时器 */
                    if (check_touch_input()) {
                        now_sec = time(NULL);
                        for (int j = 0; j < app_count; j++) {
                            if (apps[j].start_time != 0) {
                                apps[j].last_touch_time = now_sec;
                            }
                        }
                    }
                }
            }
        }

        now_sec = time(NULL);

        /* ===== 屏幕状态 + 前台应用检测（周期性，间隔由check_sec控制）===== */
        if (now_sec - last_check_sec >= g_check_sec) {
            last_check_sec = now_sec;

            /* 1. 读取屏幕状态 */
            int screen_state = get_screen_state();

            if (screen_state == -1) {
                /* sysfs不可用（设备可能正在启动/休眠恢复），跳过本次检测 */
                LOG_W("屏幕状态sysfs不可用，跳过检测");
                continue;
            }

            if (screen_state == 0) {
                /* ===== 屏幕已熄 ===== */
                if (prev_screen_state == 1) {
                    /* 从亮变熄 - 正式熄屏事件 */
                    LOG_I("屏幕已熄，重置所有应用状态");
                    for (int i = 0; i < app_count; i++) {
                        apps[i].start_time = 0;
                        apps[i].last_touch_time = 0;
                        apps[i].bg_mismatch_count = 0;
                    }
                }
                prev_screen_state = 0;
                continue;
            }

            /* screen_state == 1，屏幕是亮的 */
            if (prev_screen_state == 0) {
                /* ===== 屏幕唤醒（从熄屏到亮屏的边沿检测）===== */
                LOG_I("屏幕已唤醒，清除缓存并重置所有状态");
                /* 清除应用名缓存，强制下次dumpsys重新查询 */
                cached_top_app[0] = '\0';
                cache_expire_time = 0;
                /* 重置所有应用状态（用户休眠期间无法触摸，计时器应重新开始） */
                for (int i = 0; i < app_count; i++) {
                    apps[i].start_time = 0;
                    apps[i].last_touch_time = 0;
                    apps[i].bg_mismatch_count = 0;
                }
                prev_screen_state = 1;
                /* 不continue，继续执行下面的前台检测，立即重新评估前台应用 */
            } else {
                prev_screen_state = 1;
            }

            /* 2. 前台应用检测（节流：每check_sec秒一次） */
            char current_app[128] = {0};
            if (get_top_app_name(current_app, sizeof(current_app))) {
                /* 日志节流：只在应用变化时打印 */
                if (strcmp(current_app, last_seen_app) != 0) {
                    LOG_I("前台应用变更: %s -> %s",
                          last_seen_app[0] ? last_seen_app : "(无)", current_app);
                    strncpy(last_seen_app, current_app, sizeof(last_seen_app) - 1);
                }

                /* 应用匹配逻辑 */
                for (int i = 0; i < app_count; i++) {
                    AppConfig *app = &apps[i];

                    if (strcmp(current_app, app->package) == 0) {
                        /* 匹配到目标应用 */
                        app->bg_mismatch_count = 0;

                        if (app->start_time == 0) {
                            /* 首次检测到 - 开始跟踪 */
                            app->start_time = now_sec;
                            app->last_touch_time = now_sec;
                            LOG_I("开始跟踪: %s (超时=%ld秒)",
                                  app->package, app->limit_time_sec);
                        }

                        /* 超时检查 */
                        long elapsed = now_sec - app->last_touch_time;
                        if (elapsed >= app->limit_time_sec) {
                            LOG_I("无触摸超时，触发息屏 (应用=%s, 已无操作%ld秒)",
                                  app->package, elapsed);
                            trigger_screen_off();
                            app->start_time = 0;
                            app->last_touch_time = 0;
                        }
                    } else {
                        /* 未匹配 - 应用可能已切后台 */
                        if (app->start_time != 0) {
                            app->bg_mismatch_count++;
                            if (app->bg_mismatch_count >= BG_MISMATCH_THRESHOLD) {
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

        /* 主循环休眠10ms，降低CPU占用 */
        usleep(10000);
    }

    LOG_I("守护进程退出");
    close(epoll_fd);
    close(inotify_fd);
    for (int i = 0; i < touch_fd_count; i++) close(touch_fds[i]);
    return 0;
}
