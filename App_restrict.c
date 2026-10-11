#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <ctype.h>
#include <stdbool.h>
#include <signal.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/ioctl.h>
#include <sys/epoll.h>
#include <linux/input.h>

/* ---------- 常量 ---------- */
#define MAX_PKG_LEN 256
#define CMD_BUFFER_SIZE 4096
#define MAX_APPS 100
#define CONFIG_LINE_MAX 512
#define CONFIG_CHECK_INTERVAL 10
#define MAX_LOG_SIZE (100 * 1024)
#define SCREEN_CHECK_INTERVAL 5
#define SCREEN_OFF_WAIT_TIME 5
#define TOUCH_CHECK_INTERVAL 10
#define MAX_DEVICES 10
#define SLEEP_INTERVAL_SCREEN_OFF 30
#define LOG_SUPPRESS_INTERVAL 60

#define DEFAULT_LIMIT_TIME      (15 * 60)  /* 默认停留时限 15 分钟 */
#define TOP_PKG_CACHE_TTL       3          /* 跟踪态前台应用缓存 */
#define TOP_PKG_IDLE_CACHE_TTL  5          /* 待机态前台应用缓存 */
#define IDLE_POLL_INTERVAL      2          /* 待机轮询间隔 */
#define FULL_SCAN_BACKOFF       30         /* 4 条命令全失败后的退避 */
#define GETEVENT_RETRY_INTERVAL 5          /* getevent 启动失败重试间隔 */

#define LOG_I(fmt, ...) do { if (log_enabled) write_log("[I] " fmt, ##__VA_ARGS__); } while (0)
#define LOG_E(fmt, ...) do { if (log_enabled) write_log("[E] " fmt, ##__VA_ARGS__); } while (0)

#ifndef BITS_PER_LONG
#define BITS_PER_LONG (sizeof(long) * 8)
#endif
#define NBITS(x) ((((x) - 1) / BITS_PER_LONG) + 1)
#define test_bit(nr, addr) (((1UL << ((nr) % BITS_PER_LONG)) & (addr)[(nr) / BITS_PER_LONG]) != 0)

/* ---------- 全局状态 ---------- */
static int epfd = -1;
static int touch_fds[MAX_DEVICES];
static int touch_fd_count = 0;
static pid_t getevent_pid = -1;
static int getevent_fd = -1;
static bool use_getevent = false;

static bool log_enabled = false;
static FILE* log_fp = NULL;
static bool log_writing = false;
static char log_file_path[256] = {0};

static char cached_top_pkg[MAX_PKG_LEN] = {0};
static bool top_pkg_cache_valid = false;
static time_t last_top_pkg_time = 0;
static time_t full_scan_lock_until = 0;

static bool screen_state_cached = true;
static time_t last_screen_check = 0;

static time_t last_no_touch_log = 0;
static time_t last_cmd_fail_log = 0;
static time_t last_backlight_fail_log = 0;

typedef struct {
    char package[MAX_PKG_LEN];
    long limit_time;      /* 应用内累计停留时限（秒） */
    long no_touch_time;   /* 无触摸阈值（秒），缺省 = limit_time */
    time_t start_time;
    time_t last_touch_time;
    bool screen_off_triggered;
} AppConfig;

static AppConfig apps[MAX_APPS];
static int app_count = 0;
static time_t last_config_mtime = 0;

/* ---------- 日志 ---------- */
static char* get_timestamp(void) {
    static char buf[32];
    time_t now = time(NULL);
    struct tm* tm = localtime(&now);
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", tm);
    return buf;
}

static void ensure_log_file(void) {
    if (!log_fp && log_file_path[0]) {
        log_fp = fopen(log_file_path, "a");
        if (!log_fp) {
            fprintf(stderr, "无法打开日志文件 %s: %s\n", log_file_path, strerror(errno));
        }
    }
}

static void check_log_size(void) {
    if (log_writing || !log_fp) return;
    struct stat st;
    if (stat(log_file_path, &st) == 0 && st.st_size >= MAX_LOG_SIZE) {
        fclose(log_fp);
        log_fp = fopen(log_file_path, "w");   /* 超限清空重建 */
        if (log_fp) fclose(log_fp);
        log_fp = NULL;
    }
}

static void write_log(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    if (log_file_path[0]) {
        ensure_log_file();
        check_log_size();
        if (!log_fp) ensure_log_file();
    }
    if (log_fp) {
        log_writing = true;
        fprintf(log_fp, "[%s] ", get_timestamp());
        vfprintf(log_fp, fmt, args);
        fprintf(log_fp, "\n");
        fflush(log_fp);
        log_writing = false;
    } else {
        /* 未指定 --log= 时回落到 stderr，避免调试信息静默丢失 */
        fprintf(stderr, "[%s] ", get_timestamp());
        vfprintf(stderr, fmt, args);
        fprintf(stderr, "\n");
    }
    va_end(args);
}

/* ---------- 字符串工具 ---------- */
static char* trim(char* s) {
    while (isspace((unsigned char)*s)) s++;
    if (*s == '\0') return s;
    char* end = s + strlen(s) - 1;
    while (end > s && isspace((unsigned char)*end)) { *end = '\0'; end--; }
    return s;
}

/* ---------- 命令执行（修复 P3/P4） ---------- */
static int exec_cmd(const char* cmd, char* buf, size_t buf_size) {
    FILE* pipe = popen(cmd, "r");
    if (!pipe) {
        time_t now = time(NULL);
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("执行命令失败: %s", cmd);
            last_cmd_fail_log = now;
        }
        return -1;
    }
    if (buf && buf_size > 0) buf[0] = '\0';
    size_t total = 0;
    char tmp[512];
    size_t n;
    /* 关键：无论缓冲区是否写满，都必须读到 EOF，否则子进程阻塞在 write，
       pclose 的 waitpid 与之互相等待造成死锁 */
    while ((n = fread(tmp, 1, sizeof(tmp), pipe)) > 0) {
        if (buf && buf_size > 0 && total < buf_size - 1) {
            size_t copy = n;
            if (copy > buf_size - 1 - total) copy = buf_size - 1 - total;
            memcpy(buf + total, tmp, copy);
            total += copy;
            buf[total] = '\0';
        }
    }
    int status = pclose(pipe);
    if (status == -1) {
        time_t now = time(NULL);
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("等待命令结束失败: %s", cmd);
            last_cmd_fail_log = now;
        }
        return -1;
    }
    bool exited_ok = WIFEXITED(status) && WEXITSTATUS(status) == 0;
    if (buf == NULL) return exited_ok ? 0 : -1;
    return (total > 0) ? 0 : -1;
}

/* ---------- 前台应用识别（修复 P2） ---------- */
/* 在 text 所在行内提取第一个"形如包名"的 token：
   以字母/下划线开头，含 '.'，仅由字母数字下划线和 '.' 组成 */
static bool extract_package_from(const char* text, char* buf, size_t buf_size) {
    const char* p = text;
    while (*p && *p != '\n') {
        while (*p && *p != '\n' &&
               !(isalnum((unsigned char)*p) || *p == '_' || *p == '.')) p++;
        if (!*p || *p == '\n') break;
        const char* start = p;
        while (isalnum((unsigned char)*p) || *p == '_' || *p == '.') p++;
        size_t len = (size_t)(p - start);
        if (len >= 3 && len < buf_size &&
            memchr(start, '.', len) != NULL &&
            !isdigit((unsigned char)*start)) {
            memcpy(buf, start, len);
            buf[len] = '\0';
            return true;
        }
    }
    return false;
}

static char* get_top_app_name(char* buf, size_t buf_size, int cache_ttl) {
    if (!buf || buf_size < MAX_PKG_LEN) {
        LOG_E("无效缓冲区或大小");
        return NULL;
    }
    time_t now = time(NULL);
    if (top_pkg_cache_valid && now - last_top_pkg_time < cache_ttl) {
        snprintf(buf, buf_size, "%s", cached_top_pkg);
        return buf;
    }

    static const char* commands[] = {
        "/system/bin/dumpsys window | grep mCurrentFocus",
        "/system/bin/dumpsys window displays | grep -i mFocusedApp",
        "/system/bin/dumpsys activity activities | grep -i mActivityComponent=",
        "/system/bin/dumpsys activity | grep -i mResumedActivity"
    };
    static const char* keywords[] = {
        "mCurrentFocus=", "mFocusedApp=ActivityRecord{",
        "mActivityComponent=", "mResumedActivity:"
    };
    const int cmd_count = 4;

    /* 上一轮全链失败后进入退避，退避期内只尝试最快的第一条命令 */
    int limit = (now < full_scan_lock_until) ? 1 : cmd_count;

    for (int i = 0; i < limit; i++) {
        char out[CMD_BUFFER_SIZE];
        out[0] = '\0';
        if (exec_cmd(commands[i], out, sizeof(out)) != 0) continue;

        char* pos = out;
        char* last_match = NULL;
        size_t kw_len = strlen(keywords[i]);
        while ((pos = strstr(pos, keywords[i])) != NULL) {
            last_match = pos;
            pos += kw_len;
        }
        if (!last_match) continue;

        char* start = last_match + kw_len;
        if (extract_package_from(start, buf, buf_size)) {
            snprintf(cached_top_pkg, sizeof(cached_top_pkg), "%s", buf);
            last_top_pkg_time = now;
            top_pkg_cache_valid = true;
            full_scan_lock_until = 0;
            return buf;
        }
    }

    /* 失败结果同样入缓存（负缓存），避免进程风暴 */
    buf[0] = '\0';
    cached_top_pkg[0] = '\0';
    last_top_pkg_time = now;
    top_pkg_cache_valid = true;
    if (limit == cmd_count) full_scan_lock_until = now + FULL_SCAN_BACKOFF;
    return buf;
}

/* ---------- 时间解析（修复 P9） ---------- */
/* 成功返回秒数；失败返回 -1 */
static long parse_time(const char* time_str) {
    if (!time_str) return -1;
    while (isspace((unsigned char)*time_str)) time_str++;
    if (*time_str == '\0') return -1;

    char* endptr = NULL;
    long value = strtol(time_str, &endptr, 10);
    if (endptr == time_str || value < 0) return -1;

    while (isspace((unsigned char)*endptr)) endptr++;
    if (*endptr == '\0') return value * 60;                 /* 无后缀按分钟 */
    if ((endptr[0] == 'h' || endptr[0] == 'H') && endptr[1] == '\0') return value * 3600;
    if ((endptr[0] == 'm' || endptr[0] == 'M') && endptr[1] == '\0') return value * 60;
    if ((endptr[0] == 's' || endptr[0] == 'S') && endptr[1] == '\0') return value;
    return -1;                                              /* 非法后缀 */
}

/* ---------- 触摸设备（主路径） ---------- */
static bool find_touch_devices(void) {
    const char* input_dir = "/dev/input";
    DIR* dir = opendir(input_dir);
    if (!dir) {
        LOG_E("无法打开输入设备目录: %s", input_dir);
        return false;
    }
    touch_fd_count = 0;
    struct dirent* entry;
    while ((entry = readdir(dir)) && touch_fd_count < MAX_DEVICES) {
        if (strncmp(entry->d_name, "event", 5) == 0) {
            char path[256];
            snprintf(path, sizeof(path), "%s/%s", input_dir, entry->d_name);
            int fd = open(path, O_RDONLY | O_NONBLOCK);
            if (fd >= 0) {
                char name[256] = {0};
                if (ioctl(fd, EVIOCGNAME(sizeof(name)), name) >= 0 && !strstr(name, "uinput")) {
                    unsigned long abs_bits[NBITS(ABS_MAX)];
                    memset(abs_bits, 0, sizeof(abs_bits));
                    if (ioctl(fd, EVIOCGBIT(EV_ABS, sizeof(abs_bits)), abs_bits) >= 0) {
                        if (test_bit(ABS_MT_POSITION_X, abs_bits) ||
                            test_bit(ABS_MT_POSITION_Y, abs_bits) ||
                            test_bit(ABS_MT_TRACKING_ID, abs_bits)) {
                            touch_fds[touch_fd_count++] = fd;
                            continue;
                        }
                    }
                }
                close(fd);
            }
        }
    }
    closedir(dir);
    return touch_fd_count > 0;
}

static bool init_touch_devices(void) {
    if (epfd < 0) {
        epfd = epoll_create1(0);
        if (epfd < 0) {
            LOG_E("epoll_create1 失败: %s", strerror(errno));
            return false;
        }
    }
    if (touch_fd_count == 0 && !find_touch_devices()) {
        LOG_E("未找到触摸设备");
        return false;
    }
    for (int i = 0; i < touch_fd_count; i++) {
        struct epoll_event ev;
        memset(&ev, 0, sizeof(ev));
        ev.events = EPOLLIN;
        ev.data.fd = touch_fds[i];
        if (epoll_ctl(epfd, EPOLL_CTL_ADD, touch_fds[i], &ev) < 0) {
            LOG_E("epoll_ctl 添加触摸设备失败: %s", strerror(errno));
            for (int j = 0; j < i; j++) {
                epoll_ctl(epfd, EPOLL_CTL_DEL, touch_fds[j], NULL);
                close(touch_fds[j]);
            }
            touch_fd_count = 0;
            return false;
        }
    }
    return true;
}

/* ---------- getevent 回退（修复 P5） ---------- */
static bool init_getevent(void) {
    if (getevent_fd >= 0) return true;

    if (epfd < 0) {
        epfd = epoll_create1(0);
        if (epfd < 0) {
            LOG_E("epoll_create1 失败: %s", strerror(errno));
            return false;
        }
    }
    int pipefd[2];
    if (pipe(pipefd) < 0) {
        LOG_E("创建管道失败: %s", strerror(errno));
        return false;
    }
    pid_t pid = fork();
    if (pid < 0) {
        LOG_E("fork 失败: %s", strerror(errno));
        close(pipefd[0]);
        close(pipefd[1]);
        return false;
    }
    if (pid == 0) {
        close(pipefd[0]);
        dup2(pipefd[1], STDOUT_FILENO);
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull >= 0) { dup2(devnull, STDERR_FILENO); close(devnull); }
        close(pipefd[1]);
        execlp("getevent", "getevent", "-q", (char*)NULL);
        _exit(127);
    }
    close(pipefd[1]);
    getevent_pid = pid;
    getevent_fd = pipefd[0];

    int flags = fcntl(getevent_fd, F_GETFL, 0);
    fcntl(getevent_fd, F_SETFL, flags | O_NONBLOCK);

    struct epoll_event ev;
    memset(&ev, 0, sizeof(ev));
    ev.events = EPOLLIN;
    ev.data.fd = getevent_fd;
    if (epoll_ctl(epfd, EPOLL_CTL_ADD, getevent_fd, &ev) < 0) {
        LOG_E("epoll_ctl 添加 getevent 管道失败: %s", strerror(errno));
        close(getevent_fd);
        getevent_fd = -1;
        kill(getevent_pid, SIGKILL);
        waitpid(getevent_pid, NULL, 0);
        getevent_pid = -1;
        return false;
    }
    LOG_I("触摸设备不可用，已回退到 getevent 模式（pid=%d）", (int)getevent_pid);
    return true;
}

static void cleanup_getevent(void) {
    if (getevent_fd >= 0) {
        if (epfd >= 0) epoll_ctl(epfd, EPOLL_CTL_DEL, getevent_fd, NULL);
        close(getevent_fd);
        getevent_fd = -1;
    }
    if (getevent_pid > 0) {
        kill(getevent_pid, SIGKILL);
        waitpid(getevent_pid, NULL, 0);
        getevent_pid = -1;
    }
}

static void cleanup_touch_devices(void) {
    for (int i = 0; i < touch_fd_count; i++) {
        if (epfd >= 0) epoll_ctl(epfd, EPOLL_CTL_DEL, touch_fds[i], NULL);
        close(touch_fds[i]);
    }
    touch_fd_count = 0;
    cleanup_getevent();
    if (epfd >= 0) {
        close(epfd);
        epfd = -1;
    }
}

/* ---------- 触摸检测（修复 P7/P8，含忙循环保护） ---------- */
static bool check_touch_input(time_t* last_touch) {
    if (touch_fd_count == 0 && !use_getevent) {
        if (!init_touch_devices()) use_getevent = true;
    }
    if (use_getevent && getevent_fd < 0) {
        if (!init_getevent()) {
            sleep(GETEVENT_RETRY_INTERVAL);   /* 防止忙循环 */
            return false;
        }
    }
    if (epfd < 0) {
        sleep(GETEVENT_RETRY_INTERVAL);
        return false;
    }

    struct epoll_event events[MAX_DEVICES + 1];
    int nfds = epoll_wait(epfd, events, MAX_DEVICES + 1, TOUCH_CHECK_INTERVAL * 1000);
    if (nfds < 0) {
        if (errno == EINTR) return false;
        LOG_E("epoll_wait 失败: %s", strerror(errno));
        cleanup_touch_devices();
        use_getevent = true;
        sleep(1);                              /* 防止忙循环 */
        return false;
    }
    if (nfds <= 0) return false;

    bool touch_detected = false;
    for (int i = 0; i < nfds; i++) {
        int fd = events[i].data.fd;
        if (!use_getevent && fd != getevent_fd) {
            struct input_event ev;
            while (read(fd, &ev, sizeof(ev)) > 0) {
                if (ev.type == EV_ABS) {
                    if (ev.code == ABS_MT_POSITION_X || ev.code == ABS_MT_POSITION_Y ||
                        ev.code == ABS_MT_PRESSURE ||
                        (ev.code == ABS_MT_TRACKING_ID && ev.value != -1)) {
                        touch_detected = true;
                    }
                } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH && ev.value == 1) {
                    touch_detected = true;
                }
                /* 不再把 EV_SYN/SYN_REPORT 当作触摸，避免悬停/噪声误判 */
            }
            if (errno != EAGAIN) {
                cleanup_touch_devices();
                use_getevent = true;
                return false;
            }
        } else if (fd == getevent_fd) {
            char buf[256];
            ssize_t n;
            while ((n = read(fd, buf, sizeof(buf))) > 0) {
                touch_detected = true;
            }
            if (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK) {
                cleanup_touch_devices();
                return false;
            }
        }
    }
    if (touch_detected) {
        *last_touch = time(NULL);              /* 返回真实触摸时刻 */
        return true;
    }
    return false;
}

/* ---------- 应用状态管理 ---------- */
static AppConfig* find_app(const char* package) {
    for (int i = 0; i < app_count; i++) {
        if (strcmp(apps[i].package, package) == 0) return &apps[i];
    }
    return NULL;
}

static void reset_app(AppConfig* app, const char* reason) {
    if (app->start_time != 0) {
        LOG_I("应用 %s %s，重置状态", app->package, reason);
    }
    app->start_time = 0;
    app->last_touch_time = 0;
    app->screen_off_triggered = false;
}

static void reset_all_apps(const char* reason) {
    for (int i = 0; i < app_count; i++) reset_app(&apps[i], reason);
}

/* ---------- 配置加载（修复 P10/P11） ---------- */
static int load_config(const char* config_path) {
    FILE* fp = fopen(config_path, "r");
    if (!fp) {
        LOG_E("无法打开配置文件: %s", config_path);
        return -1;
    }
    AppConfig temp_apps[MAX_APPS];
    int temp_count = 0;
    AppConfig* cur = NULL;
    char line[CONFIG_LINE_MAX];
    int line_no = 0;

    while (fgets(line, sizeof(line), fp)) {
        line_no++;
        char* trimmed = trim(line);            /* 去首尾空白与 \r */
        if (*trimmed == '\0' || *trimmed == '#') continue;

        char* eq = strchr(trimmed, '=');       /* 只在第一个 '=' 处切分 */
        if (!eq) {
            LOG_E("配置第 %d 行缺少 '='，已忽略: %s", line_no, trimmed);
            continue;
        }
        *eq = '\0';
        char* key = trim(trimmed);
        char* value = trim(eq + 1);
        if (*key == '\0' || *value == '\0') continue;

        if (strcmp(key, "package") == 0) {
            if (strlen(value) >= MAX_PKG_LEN) {
                LOG_E("配置第 %d 行包名过长，已忽略", line_no);
                cur = NULL;
                continue;
            }
            cur = NULL;
            for (int i = 0; i < temp_count; i++) {
                if (strcmp(temp_apps[i].package, value) == 0) { cur = &temp_apps[i]; break; }
            }
            if (cur) continue;                 /* 同名复用 */
            if (temp_count >= MAX_APPS) {
                LOG_E("应用数量超过 %d，忽略 %s", MAX_APPS, value);
                cur = NULL;
                continue;
            }
            cur = &temp_apps[temp_count++];
            memset(cur, 0, sizeof(*cur));
            snprintf(cur->package, sizeof(cur->package), "%s", value);
            cur->limit_time = DEFAULT_LIMIT_TIME;
            cur->no_touch_time = -1;           /* -1 表示未配置，稍后取 limit_time */
            /* 从旧配置继承运行状态，保证热更新不丢计时 */
            AppConfig* old = find_app(value);
            if (old) {
                cur->start_time = old->start_time;
                cur->last_touch_time = old->last_touch_time;
                cur->screen_off_triggered = old->screen_off_triggered;
            }
        } else if (strcmp(key, "limit_time") == 0 || strcmp(key, "no_touch_time") == 0) {
            if (!cur) {
                LOG_E("配置第 %d 行 %s 出现在 package 之前，已忽略", line_no, key);
                continue;
            }
            long v = parse_time(value);
            if (v < 0) {
                LOG_E("配置第 %d 行 %s 值非法: %s，保持默认", line_no, key, value);
                continue;
            }
            if (strcmp(key, "limit_time") == 0) cur->limit_time = v;
            else cur->no_touch_time = v;
        } else {
            LOG_E("配置第 %d 行未知配置项: %s", line_no, key);
        }
    }
    fclose(fp);

    if (temp_count == 0) {
        LOG_E("配置文件中未找到有效应用，保持原配置不变");
        return -1;
    }
    for (int i = 0; i < temp_count; i++) {
        if (temp_apps[i].no_touch_time < 0) temp_apps[i].no_touch_time = temp_apps[i].limit_time;
    }
    memcpy(apps, temp_apps, sizeof(AppConfig) * temp_count);
    app_count = temp_count;
    return 0;
}

static bool check_config_updated(const char* config_path) {
    struct stat st;
    if (stat(config_path, &st) != 0) {
        LOG_E("无法获取配置文件状态: %s", config_path);
        return false;
    }
    if (st.st_mtime > last_config_mtime) {
        last_config_mtime = st.st_mtime;
        return true;
    }
    return false;
}

/* ---------- 屏幕状态（修复 P6/P12） ---------- */
static void invalidate_screen_cache(void) {
    last_screen_check = 0;
}

static bool is_screen_on(void) {
    time_t now = time(NULL);
    if (last_screen_check != 0 && now - last_screen_check < SCREEN_CHECK_INTERVAL) {
        return screen_state_cached;
    }
    /* 1) 背光节点可读：直接以亮度为准，避免二次 dumpsys 误判 */
    const char* backlight_path = "/sys/class/backlight/panel0-backlight/brightness";
    int fd = open(backlight_path, O_RDONLY);
    if (fd >= 0) {
        char buf[32] = {0};
        ssize_t n = read(fd, buf, sizeof(buf) - 1);
        close(fd);
        if (n > 0) {
            long value = strtol(buf, NULL, 10);
            screen_state_cached = (value > 0);
            last_screen_check = now;
            return screen_state_cached;
        }
    }
    /* 2) 回退：dumpsys display */
    char out[512];
    out[0] = '\0';
    if (exec_cmd("dumpsys display | grep mScreenState", out, sizeof(out)) == 0) {
        if (strstr(out, "mScreenState=ON")) {
            screen_state_cached = true; last_screen_check = now; return true;
        }
        if (strstr(out, "mScreenState=OFF")) {
            screen_state_cached = false; last_screen_check = now; return false;
        }
    }
    /* 3) 回退：dumpsys window */
    out[0] = '\0';
    if (exec_cmd("dumpsys window | grep mScreenOn", out, sizeof(out)) == 0) {
        if (strstr(out, "mScreenOnEarly=true")) {
            screen_state_cached = true; last_screen_check = now; return true;
        }
        if (strstr(out, "mScreenOnEarly=false")) {
            screen_state_cached = false; last_screen_check = now; return false;
        }
    }
    /* 4) 回退：deviceidle */
    out[0] = '\0';
    if (exec_cmd("dumpsys deviceidle get screen 2>/dev/null", out, sizeof(out)) == 0) {
        if (strstr(out, "true")) {
            screen_state_cached = true; last_screen_check = now; return true;
        }
        if (strstr(out, "false")) {
            screen_state_cached = false; last_screen_check = now; return false;
        }
    }
    /* 无法判定时保守认为亮屏：继续监控无副作用，误判成灭屏才会破坏跟踪 */
    screen_state_cached = true;
    last_screen_check = now;
    return true;
}

/* ---------- 息屏触发（修复 P12/P13） ---------- */
static void trigger_screen_off(AppConfig* app) {
    if (!is_screen_on()) {
        app->screen_off_triggered = true;
        app->start_time = 0;
        app->last_touch_time = 0;
        LOG_I("应用 %s 无触控超时时限，屏幕已关闭", app->package);
        return;
    }
    if (exec_cmd("input keyevent 26", NULL, 0) == 0) {
        sleep(SCREEN_OFF_WAIT_TIME);
        invalidate_screen_cache();             /* 强制刷新，避免读到旧缓存 */
        if (!is_screen_on()) {
            app->screen_off_triggered = true;
            app->start_time = 0;
            app->last_touch_time = 0;
            LOG_I("应用 %s 无触控超时时限，触发屏幕息屏", app->package);
            return;
        }
    }
    LOG_E("无法触发屏幕息屏，请检查设备权限或背光文件路径");
    /* 失败后给宽限期，避免每轮重试 input 命令 */
    app->last_touch_time = time(NULL);
}

/* ---------- 主循环（修复 P1/P8） ---------- */
int main(int argc, char* argv[]) {
    char* config_path = NULL;
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "--config=", 9) == 0) {
            config_path = argv[i] + 9;
        } else if (strncmp(argv[i], "--log=", 6) == 0) {
            strncpy(log_file_path, argv[i] + 6, sizeof(log_file_path) - 1);
            log_file_path[sizeof(log_file_path) - 1] = '\0';
        } else if (strncmp(argv[i], "--debug=", 8) == 0) {
            log_enabled = strcmp(argv[i] + 8, "true") == 0;
        }
    }
    if (!config_path) {
        fprintf(stderr, "错误：必须提供 --config=<路径>\n");
        return 1;
    }
    if (log_enabled && log_file_path[0]) {
        ensure_log_file();
        if (!log_fp) {
            fprintf(stderr, "无法打开日志文件: %s\n", log_file_path);
            return 1;
        }
    } else if (log_enabled) {
        fprintf(stderr, "提示：未指定 --log=，日志将输出到 stderr\n");
    }
    if (load_config(config_path) != 0) {
        if (log_fp) fclose(log_fp);
        return 1;
    }

    LOG_I("启动应用时间限制守护进程（无触控息屏模式），共加载 %d 个应用", app_count);
    for (int i = 0; i < app_count; i++) {
        LOG_I("  应用 %s：停留时限 %lds，无触摸阈值 %lds",
              apps[i].package, apps[i].limit_time, apps[i].no_touch_time);
    }

    bool tracking_active = false;
    time_t last_config_check = 0;
    bool last_logged_screen_state = true;
    char current_app[MAX_PKG_LEN];

    while (1) {
        /* ① 屏幕状态（带 5s 缓存；背光节点可读时不产生 dumpsys） */
        bool screen_on = is_screen_on();
        if (screen_on != last_logged_screen_state) {
            LOG_I("屏幕状态变为: %s", screen_on ? "开启" : "关闭");
            last_logged_screen_state = screen_on;
        }
        if (!screen_on) {
            reset_all_apps("屏幕关闭");
            cleanup_touch_devices();
            use_getevent = false;
            tracking_active = false;
            sleep(SLEEP_INTERVAL_SCREEN_OFF);
            continue;
        }

        /* ② 配置热更新（每 10s 检查一次 mtime，开销可忽略） */
        time_t now = time(NULL);
        if (now - last_config_check >= CONFIG_CHECK_INTERVAL) {
            if (check_config_updated(config_path)) {
                LOG_I("检测到配置文件更新，重新加载");
                load_config(config_path);
            }
            last_config_check = now;
        }

        /* ③ 前台应用识别（带缓存：跟踪态 3s / 待机态 5s） */
        current_app[0] = '\0';
        if (get_top_app_name(current_app, sizeof(current_app),
                             tracking_active ? TOP_PKG_CACHE_TTL : TOP_PKG_IDLE_CACHE_TTL) == NULL) {
            sleep(IDLE_POLL_INTERVAL);
            continue;
        }

        AppConfig* cur = current_app[0] ? find_app(current_app) : NULL;
        if (!cur) {
            /* ④ 不在受管应用内（如游戏）：不碰输入设备、不做触摸检测，进入待机轮询 */
            if (tracking_active) {
                reset_all_apps("切换到后台");
                cleanup_touch_devices();
                use_getevent = false;
                tracking_active = false;
            }
            sleep(IDLE_POLL_INTERVAL);
            continue;
        }

        /* ⑤ 受管应用在前台：进入/维持跟踪 */
        tracking_active = true;
        if (touch_fd_count == 0 && !use_getevent) init_touch_devices();

        time_t last_touch = 0;
        bool has_touch = check_touch_input(&last_touch);
        now = time(NULL);                      /* 重新取时间，消除 epoll 阻塞造成的偏差 */

        for (int i = 0; i < app_count; i++) {
            if (&apps[i] != cur && apps[i].start_time != 0) {
                reset_app(&apps[i], "切换到后台");
            }
        }

        if (cur->start_time == 0) {
            cur->start_time = now;
            cur->last_touch_time = now;
            cur->screen_off_triggered = false;
            LOG_I("开始跟踪 %s（停留时限 %lds，无触摸阈值 %lds）",
                  cur->package, cur->limit_time, cur->no_touch_time);
        } else {
            if (has_touch && last_touch > cur->last_touch_time) {
                cur->last_touch_time = last_touch;
            }
            long stay = (long)(now - cur->start_time);
            long idle = (long)(now - cur->last_touch_time);
            if (!cur->screen_off_triggered &&
                stay >= cur->limit_time && idle >= cur->no_touch_time) {
                LOG_I("应用 %s 停留 %lds、无触摸 %lds，触发息屏", cur->package, stay, idle);
                trigger_screen_off(cur);
            }
        }
    }

    cleanup_touch_devices();
    if (log_fp) fclose(log_fp);
    return 0;
}
