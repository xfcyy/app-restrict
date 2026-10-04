/*
 * App_restrict - 短视频应用无触控息屏守护进程
 *
 * 功能：
 *   监听配置文件中指定的包名（如抖音、B站等），当这些应用处于前台，
 *   且超过配置的时间阈值没有触摸操作时，自动触发屏幕关闭（电源键），
 *   防止长时间无人操作导致烧屏。
 *
 * 设计原则：
 *   1. 前台应用检测间隔拉长（15s），只使用轻量级 dumpsys window 命令。
 *   2. 屏幕状态优先读 sysfs，避免频繁 dumpsys。
 *   3. 触摸事件使用 epoll + 短超时轮询（1 秒）。
 *   4. 只在目标应用位于前台时才轮询触摸设备，其余时间低功耗休眠。
 *   5. 目标应用不在前台时，不执行任何 dumpsys 命令。
 *
 * 用法：
 *   App_restrict --config=/path/to/config [--log=/path/to/log] [--debug=true]
 *
 * 配置文件格式：
 *   package=com.ss.android.ugc.aweme
 *   limit_time=5m
 *   package=com.example.another
 *   limit_time=10m
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <time.h>
#include <unistd.h>
#include <ctype.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>
#include <glob.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/epoll.h>
#include <sys/wait.h>
#include <linux/input.h>

#define MAX_PKG_LEN 256
#define CMD_BUFFER_SIZE 1024
#define MAX_APPS 100
#define CONFIG_LINE_MAX 512
#define MAX_LOG_SIZE (100 * 1024)
#define LOG_SUPPRESS_INTERVAL 60
#define MAX_DEVICES 16

/* 时序参数（秒 / 毫秒） */
#define SCREEN_CHECK_INTERVAL     10   /* 屏幕状态检查间隔 */
#define FG_CHECK_INTERVAL         15   /* 前台应用检查间隔 */
#define CONFIG_CHECK_INTERVAL     30   /* 配置文件检查间隔 */
#define IDLE_SLEEP_SEC            5    /* 目标应用不在前台时的休眠 */
#define TOUCH_EPOLL_TIMEOUT_MS    1000 /* 触摸轮询超时 */
#define SCREEN_OFF_VERIFY_WAIT    3    /* 熄屏后等待验证时间 */

#define DEFAULT_LIMIT_SEC (15 * 60)

#ifndef BITS_PER_LONG
#define BITS_PER_LONG (sizeof(long) * 8)
#endif
#define NBITS(x) ((((x) - 1) / BITS_PER_LONG) + 1)
#define test_bit(nr, addr) \
    (((1UL << ((nr) % BITS_PER_LONG)) & (addr)[(nr) / BITS_PER_LONG]) != 0)

/* ---------- 全局状态 ---------- */

static bool log_enabled = false;
static FILE *log_fp = NULL;
static char log_file_path[256] = {0};
static char config_file_path[256] = {0};
static time_t last_cmd_fail_log = 0;

typedef struct {
    char package[MAX_PKG_LEN];
    time_t limit_time;   /* 无触摸阈值（秒） */
    time_t last_touch;   /* 最后一次触摸时间 */
    bool tracking;       /* 是否正在跟踪 */
    bool triggered;      /* 是否已触发过熄屏（防止重复触发） */
} AppConfig;

static AppConfig apps[MAX_APPS];
static int app_count = 0;
static time_t last_config_mtime = 0;

/* 触摸设备 */
static int epfd = -1;
static int touch_fds[MAX_DEVICES];
static int touch_fd_count = 0;

/* ---------- 日志 ---------- */

#define LOG_I(fmt, ...) do { if (log_enabled) write_log("[I] " fmt, ##__VA_ARGS__); } while (0)
#define LOG_E(fmt, ...) do { if (log_enabled) write_log("[E] " fmt, ##__VA_ARGS__); } while (0)

static const char *timestamp_str(void) {
    static char buf[32];
    time_t now = time(NULL);
    struct tm tm;
    localtime_r(&now, &tm);
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", &tm);
    return buf;
}

static void rotate_log_if_needed(void) {
    if (!log_fp) return;
    struct stat st;
    if (stat(log_file_path, &st) != 0) return;
    if (st.st_size < MAX_LOG_SIZE) return;
    fclose(log_fp);
    log_fp = fopen(log_file_path, "w");
    if (log_fp) fclose(log_fp);
    log_fp = fopen(log_file_path, "a");
}

static void write_log(const char *fmt, ...) {
    if (!log_fp) {
        if (!log_file_path[0]) return;
        log_fp = fopen(log_file_path, "a");
        if (!log_fp) return;
    }
    rotate_log_if_needed();
    if (!log_fp) return;
    va_list args;
    va_start(args, fmt);
    fprintf(log_fp, "[%s] ", timestamp_str());
    vfprintf(log_fp, fmt, args);
    fprintf(log_fp, "\n");
    fflush(log_fp);
    va_end(args);
}

/* ---------- 命令执行 ---------- */

static int exec_cmd(const char *cmd, char *buf, size_t bufsize) {
    FILE *p = popen(cmd, "r");
    if (!p) {
        time_t now = time(NULL);
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("popen 失败: %s", strerror(errno));
            last_cmd_fail_log = now;
        }
        if (buf && bufsize) buf[0] = '\0';
        return -1;
    }
    if (buf && bufsize) {
        size_t n = fread(buf, 1, bufsize - 1, p);
        buf[n] = '\0';
    }
    int rc = pclose(p);
    if (rc == -1) return -1;
    if (WIFEXITED(rc)) return WEXITSTATUS(rc);
    return -1;
}

/* ---------- 前台应用检测 ---------- */

/*
 * 从 dumpsys 输出的一行中解析包名。
 * 形如：mCurrentFocus=Window{abc1234 u0 com.pkg/com.pkg.Activity}
 *       mFocusedApp=ActivityRecord{... u0 com.pkg/.Activity t123}
 *       mResumedActivity: ActivityRecord{... u0 com.pkg/.Activity t123}
 */
static bool parse_package(const char *line, char *out, size_t outsize) {
    if (!line || !out || outsize == 0) return false;

    const char *slash = strchr(line, '/');
    if (!slash) return false;

    const char *start = slash - 1;
    while (start >= line &&
           (isalnum((unsigned char)*start) || *start == '.' || *start == '_')) {
        start--;
    }
    start++;

    if (start >= slash) return false;
    size_t len = (size_t)(slash - start);
    if (len == 0 || len >= outsize) return false;

    bool has_dot = false;
    for (size_t i = 0; i < len; i++) {
        char c = start[i];
        if (c == '.') has_dot = true;
        if (!(isalnum((unsigned char)c) || c == '.' || c == '_')) return false;
    }
    if (!has_dot) return false;

    memcpy(out, start, len);
    out[len] = '\0';
    return true;
}

/*
 * 获取当前前台应用包名。
 * 只使用轻量级命令，避免 dumpsys activity activities 长时间持有 AMS 锁。
 * 返回 true 表示成功解析出包名。
 */
static bool get_foreground_package(char *out, size_t outsize) {
    if (!out || outsize == 0) return false;
    out[0] = '\0';

    char buf[CMD_BUFFER_SIZE];

    /* 优先级 1：mCurrentFocus（最轻） */
    if (exec_cmd("/system/bin/dumpsys window 2>/dev/null | grep -m1 mCurrentFocus",
                 buf, sizeof(buf)) == 0) {
        char *p = strstr(buf, "mCurrentFocus=");
        if (p && parse_package(p + 15, out, outsize)) return true;
    }

    /* 优先级 2：mFocusedApp */
    if (exec_cmd("/system/bin/dumpsys window 2>/dev/null | grep -m1 mFocusedApp",
                 buf, sizeof(buf)) == 0) {
        char *p = strstr(buf, "mFocusedApp=");
        if (p && parse_package(p + 12, out, outsize)) return true;
    }

    /* 优先级 3：mResumedActivity（只 grep 一行，不 dump 整个 activity 栈） */
    if (exec_cmd("/system/bin/dumpsys activity 2>/dev/null | grep -m1 mResumedActivity",
                 buf, sizeof(buf)) == 0) {
        char *p = strstr(buf, "mResumedActivity:");
        if (p && parse_package(p + 16, out, outsize)) return true;
    }

    out[0] = '\0';
    return false;
}

/* ---------- 屏幕状态 ---------- */

/*
 * 检测屏幕是否亮着。
 * 优先读 sysfs，失败时回退到 dumpsys power。
 */
static bool get_screen_state(void) {
    /* 优先 sysfs，快速且不涉及 system_server */
    glob_t g;
    bool found = false;
    bool on = true;

    if (glob("/sys/class/backlight/*/brightness", 0, NULL, &g) == 0) {
        for (size_t i = 0; i < g.gl_pathc; i++) {
            int fd = open(g.gl_pathv[i], O_RDONLY);
            if (fd < 0) continue;
            char buf[32] = {0};
            ssize_t r = read(fd, buf, sizeof(buf) - 1);
            close(fd);
            if (r > 0) {
                on = (strtol(buf, NULL, 10) > 0);
                found = true;
                break;
            }
        }
        globfree(&g);
    }

    if (!found) {
        int fd = open("/sys/class/leds/lcd-backlight/brightness", O_RDONLY);
        if (fd >= 0) {
            char buf[32] = {0};
            ssize_t r = read(fd, buf, sizeof(buf) - 1);
            close(fd);
            if (r > 0) {
                on = (strtol(buf, NULL, 10) > 0);
                found = true;
            }
        }
    }

    if (found) return on;

    /* 回退：dumpsys power 只取一行 */
    char out[512] = {0};
    if (exec_cmd("/system/bin/dumpsys power 2>/dev/null | grep -m1 mWakefulness",
                 out, sizeof(out)) == 0) {
        if (strstr(out, "mWakefulness=Awake")) return true;
        if (strstr(out, "mWakefulness=Asleep") ||
            strstr(out, "mWakefulness=Dozing")) return false;
    }
    return true; /* 未知时保守假设屏幕亮着 */
}

/* ---------- 触摸检测 ---------- */

static void close_touch_devices(void) {
    for (int i = 0; i < touch_fd_count; i++) {
        close(touch_fds[i]);
    }
    touch_fd_count = 0;
    if (epfd >= 0) {
        close(epfd);
        epfd = -1;
    }
}

static bool find_touch_devices(void) {
    DIR *dir = opendir("/dev/input");
    if (!dir) return false;

    touch_fd_count = 0;
    struct dirent *entry;
    while ((entry = readdir(dir)) && touch_fd_count < MAX_DEVICES) {
        if (strncmp(entry->d_name, "event", 5) != 0) continue;

        char path[256];
        snprintf(path, sizeof(path), "/dev/input/%s", entry->d_name);
        int fd = open(path, O_RDONLY | O_NONBLOCK);
        if (fd < 0) continue;

        char name[256] = {0};
        if (ioctl(fd, EVIOCGNAME(sizeof(name)), name) < 0 ||
            strstr(name, "uinput")) {
            close(fd);
            continue;
        }

        unsigned long abs_bits[NBITS(ABS_MAX)];
        memset(abs_bits, 0, sizeof(abs_bits));
        if (ioctl(fd, EVIOCGBIT(EV_ABS, sizeof(abs_bits)), abs_bits) < 0) {
            close(fd);
            continue;
        }

        if (test_bit(ABS_MT_POSITION_X, abs_bits) ||
            test_bit(ABS_MT_POSITION_Y, abs_bits) ||
            test_bit(ABS_MT_TRACKING_ID, abs_bits)) {
            touch_fds[touch_fd_count++] = fd;
        } else {
            close(fd);
        }
    }
    closedir(dir);
    return touch_fd_count > 0;
}

static bool init_touch_devices(void) {
    if (epfd >= 0 && touch_fd_count > 0) return true;
    close_touch_devices();

    epfd = epoll_create1(0);
    if (epfd < 0) return false;

    if (!find_touch_devices()) {
        close_touch_devices();
        return false;
    }

    struct epoll_event ev;
    for (int i = 0; i < touch_fd_count; i++) {
        ev.events = EPOLLIN;
        ev.data.fd = touch_fds[i];
        if (epoll_ctl(epfd, EPOLL_CTL_ADD, touch_fds[i], &ev) < 0) {
            close_touch_devices();
            return false;
        }
    }
    return true;
}

/*
 * 在 timeout_ms 内等待触摸事件。
 * 返回 true 表示检测到触摸，false 表示超时或无触摸。
 */
static bool poll_touch(int timeout_ms) {
    if (epfd < 0 && !init_touch_devices()) {
        return false;
    }

    struct epoll_event events[MAX_DEVICES];
    int n = epoll_wait(epfd, events, MAX_DEVICES, timeout_ms);
    if (n <= 0) return false;

    bool touched = false;
    struct input_event ev;
    for (int i = 0; i < n; i++) {
        int fd = events[i].data.fd;
        while (read(fd, &ev, sizeof(ev)) == (ssize_t)sizeof(ev)) {
            if (ev.type == EV_ABS &&
                (ev.code == ABS_MT_TRACKING_ID ||
                 ev.code == ABS_MT_POSITION_X ||
                 ev.code == ABS_MT_POSITION_Y ||
                 ev.code == ABS_MT_PRESSURE ||
                 ev.code == ABS_MT_SLOT)) {
                touched = true;
            } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH && ev.value == 1) {
                touched = true;
            }
        }
    }
    return touched;
}

/* ---------- 熄屏 ---------- */

static void trigger_screen_off(void) {
    /* KEYCODE_POWER = 26 */
    if (exec_cmd("/system/bin/input keyevent 26", NULL, 0) == 0) {
        sleep(SCREEN_OFF_VERIFY_WAIT);
        return;
    }
    /* 备用命令 */
    exec_cmd("/system/bin/input keyevent KEYCODE_POWER", NULL, 0);
    sleep(SCREEN_OFF_VERIFY_WAIT);
}

/* ---------- 配置解析 ---------- */

static long parse_time_str(const char *s) {
    if (!s) return 0;
    char *end = NULL;
    long v = strtol(s, &end, 10);
    if (end == s || v <= 0) return 0;
    switch (*end) {
        case 'h': case 'H': return v * 3600;
        case 'm': case 'M': return v * 60;
        case 's': case 'S': return v;
        default:            return v * 60; /* 无单位默认分钟 */
    }
}

static void trim_inplace(char *s) {
    if (!s) return;
    char *p = s;
    while (isspace((unsigned char)*p)) p++;
    if (p != s) memmove(s, p, strlen(p) + 1);
    size_t len = strlen(s);
    while (len > 0 && isspace((unsigned char)s[len - 1])) {
        s[--len] = '\0';
    }
}

static int load_config(const char *path) {
    FILE *fp = fopen(path, "r");
    if (!fp) {
        LOG_E("无法打开配置文件: %s (%s)", path, strerror(errno));
        return -1;
    }

    AppConfig tmp[MAX_APPS];
    int n = 0;
    AppConfig *cur = NULL;
    char line[CONFIG_LINE_MAX];

    while (fgets(line, sizeof(line), fp)) {
        trim_inplace(line);
        if (line[0] == '\0' || line[0] == '#') continue;

        char *eq = strchr(line, '=');
        if (!eq) continue;
        *eq = '\0';
        char *key = line;
        char *val = eq + 1;
        trim_inplace(key);
        trim_inplace(val);
        if (key[0] == '\0') continue;

        if (strcmp(key, "package") == 0) {
            if (n >= MAX_APPS) continue;
            cur = &tmp[n++];
            memset(cur, 0, sizeof(*cur));
            strncpy(cur->package, val, MAX_PKG_LEN - 1);
            cur->limit_time = DEFAULT_LIMIT_SEC;
            /* 从旧数组继承运行时状态 */
            for (int i = 0; i < app_count; i++) {
                if (strcmp(apps[i].package, cur->package) == 0) {
                    cur->last_touch = apps[i].last_touch;
                    cur->tracking   = apps[i].tracking;
                    cur->triggered  = apps[i].triggered;
                    break;
                }
            }
        } else if (cur && strcmp(key, "limit_time") == 0) {
            long v = parse_time_str(val);
            if (v > 0) cur->limit_time = (time_t)v;
        }
    }
    fclose(fp);

    /* 原子替换 */
    if (n < app_count) {
        memset(&apps[n], 0, sizeof(AppConfig) * (app_count - n));
    }
    memcpy(apps, tmp, sizeof(AppConfig) * n);
    app_count = n;

    LOG_I("加载配置: %d 个应用", n);
    for (int i = 0; i < n; i++) {
        LOG_I("  %s limit=%ld 秒",
              apps[i].package, (long)apps[i].limit_time);
    }
    return 0;
}

/* ---------- 主程序 ---------- */

static void usage(const char *prog) {
    fprintf(stderr,
            "用法: %s --config=<路径> [--log=<路径>] [--debug=true|false]\n",
            prog);
}

int main(int argc, char *argv[]) {
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "--config=", 9) == 0) {
            strncpy(config_file_path, argv[i] + 9, sizeof(config_file_path) - 1);
        } else if (strncmp(argv[i], "--log=", 6) == 0) {
            strncpy(log_file_path, argv[i] + 6, sizeof(log_file_path) - 1);
        } else if (strncmp(argv[i], "--debug=", 8) == 0) {
            log_enabled = (strcmp(argv[i] + 8, "true") == 0);
        } else {
            usage(argv[0]);
            return 1;
        }
    }

    if (config_file_path[0] == '\0') {
        usage(argv[0]);
        return 1;
    }

    if (log_enabled && log_file_path[0]) {
        log_fp = fopen(log_file_path, "a");
        if (!log_fp) {
            fprintf(stderr, "无法打开日志文件 %s: %s\n",
                    log_file_path, strerror(errno));
            return 1;
        }
    }

    if (load_config(config_file_path) != 0) {
        if (log_fp) fclose(log_fp);
        return 1;
    }
    if (app_count == 0) {
        LOG_E("配置文件中没有有效应用");
        if (log_fp) fclose(log_fp);
        return 1;
    }

    struct stat st;
    if (stat(config_file_path, &st) == 0) {
        last_config_mtime = st.st_mtime;
    }

    LOG_I("启动应用时间限制守护进程");

    /* 运行时状态 */
    bool screen_on = true;
    time_t last_screen_check = 0;
    time_t last_fg_check = 0;
    time_t last_cfg_check = 0;
    char current_pkg[MAX_PKG_LEN] = {0};
    AppConfig *active_app = NULL;

    while (1) {
        time_t now = time(NULL);

        /* --- 1. 屏幕状态检查 --- */
        if (now - last_screen_check >= SCREEN_CHECK_INTERVAL) {
            bool s = get_screen_state();
            if (s != screen_on) {
                LOG_I("屏幕状态: %s", s ? "亮" : "灭");
            }
            screen_on = s;
            last_screen_check = now;
        }

        /* --- 屏幕关闭：重置所有状态，休眠 --- */
        if (!screen_on) {
            for (int i = 0; i < app_count; i++) {
                if (apps[i].tracking) {
                    LOG_I("屏幕关闭，停止跟踪 %s", apps[i].package);
                }
                apps[i].tracking   = false;
                apps[i].triggered  = false;
                apps[i].last_touch = 0;
            }
            active_app = NULL;
            current_pkg[0] = '\0';
            close_touch_devices();
            sleep(IDLE_SLEEP_SEC);
            continue;
        }

        /* --- 2. 配置检查 --- */
        if (now - last_cfg_check >= CONFIG_CHECK_INTERVAL) {
            struct stat cst;
            if (stat(config_file_path, &cst) == 0 &&
                cst.st_mtime > last_config_mtime) {
                LOG_I("配置文件已更新，重新加载");
                last_config_mtime = cst.st_mtime;
                load_config(config_file_path);
                /* 重新匹配 active_app */
                active_app = NULL;
                for (int i = 0; i < app_count; i++) {
                    if (strcmp(current_pkg, apps[i].package) == 0) {
                        active_app = &apps[i];
                        break;
                    }
                }
            }
            last_cfg_check = now;
        }

        /* --- 3. 前台应用检查 --- */
        if (now - last_fg_check >= FG_CHECK_INTERVAL) {
            char pkg[MAX_PKG_LEN] = {0};
            if (get_foreground_package(pkg, sizeof(pkg)) && pkg[0]) {
                if (strcmp(pkg, current_pkg) != 0) {
                    strncpy(current_pkg, pkg, sizeof(current_pkg) - 1);
                    current_pkg[sizeof(current_pkg) - 1] = '\0';
                    LOG_I("前台应用: %s", current_pkg);

                    /* 切换到新的目标应用 */
                    AppConfig *new_active = NULL;
                    for (int i = 0; i < app_count; i++) {
                        if (strcmp(current_pkg, apps[i].package) == 0) {
                            new_active = &apps[i];
                            break;
                        }
                    }

                    if (new_active != active_app) {
                        if (active_app && active_app->tracking) {
                            LOG_I("停止跟踪 %s", active_app->package);
                            active_app->tracking   = false;
                            active_app->triggered  = false;
                            active_app->last_touch = 0;
                        }
                        active_app = new_active;
                        if (active_app) {
                            active_app->tracking   = true;
                            active_app->triggered  = false;
                            active_app->last_touch = now;
                            LOG_I("开始跟踪 %s (limit=%ld 秒)",
                                  active_app->package,
                                  (long)active_app->limit_time);
                        }
                    }
                }
            }
            /* 命令失败时保留旧的 current_pkg，不误判为无前台应用 */
            last_fg_check = now;
        }

        /* --- 4. 触摸轮询与超时判断 --- */
        if (active_app) {
            if (poll_touch(TOUCH_EPOLL_TIMEOUT_MS)) {
                active_app->last_touch = time(NULL);
                active_app->triggered  = false; /* 用户还醒着，允许后续再次触发 */
            }

            time_t t_now = time(NULL);
            if (!active_app->triggered &&
                t_now - active_app->last_touch >= active_app->limit_time) {
                LOG_I("%s 超过 %ld 秒无触摸，触发熄屏",
                      active_app->package, (long)active_app->limit_time);
                trigger_screen_off();
                active_app->triggered = true;
                /* 立即重新检查屏幕状态 */
                last_screen_check = 0;
            }
        } else {
            /* 目标应用不在前台，低功耗休眠 */
            sleep(2);
        }
    }

    close_touch_devices();
    if (log_fp) fclose(log_fp);
    return 0;
}
