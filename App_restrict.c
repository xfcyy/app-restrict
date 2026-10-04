#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <ctype.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>
#include <linux/input.h>
#include <sys/epoll.h>
#include <stdarg.h>     /* Fix5: 补充缺失的头文件 */
#include <signal.h>     /* Fix2: exec_cmd超时机制需要 */
#include <poll.h>       /* Fix2: exec_cmd超时机制需要 */
#include <sys/wait.h>   /* Fix2: exec_cmd超时机制需要 */
#include <sys/resource.h> /* Aggressive: 进程优先级管理 */
#include <sys/inotify.h>
#include <sys/prctl.h>
#include <dlfcn.h>  /* Aggressive: inotify配置文件监控 */

/* ========== 基础定义 ========== */
#define MAX_PKG_LEN 256
#define CMD_BUFFER_SIZE 1024
#define MAX_APPS 100
#define CONFIG_LINE_MAX 512
#define MAX_LOG_SIZE (100 * 1024)
#define MAX_DEVICES 10
#define SCREEN_OFF_WAIT_TIME 5
#define SLEEP_INTERVAL_SCREEN_OFF 30
#define LOG_SUPPRESS_INTERVAL 60
#define CMD_TIMEOUT_SEC 3          /* Fix2: exec_cmd超时时间(秒) */

/* ========== 激进优化: 自适应轮询参数 ========== */
/* 正常模式: 快速响应 */
#define TOUCH_CHECK_INTERVAL_NORMAL 5
/* 空闲模式(无触摸>30s): 降低轮询频率省电 */
#define TOUCH_CHECK_INTERVAL_IDLE 10
/* 深度空闲模式(无触摸>60s): 进一步降低频率 */
#define TOUCH_CHECK_INTERVAL_DEEP_IDLE 15
/* 自适应切换阈值 */
#define IDLE_THRESHOLD_SHORT 30   /* 30秒无触摸 -> 空闲模式 */
#define IDLE_THRESHOLD_LONG 60    /* 60秒无触摸 -> 深度空闲模式 */
/* 自适应缓存TTL扩展倍数 */
#define CACHE_TTL_IDLE_MULTIPLIER 3  /* 空闲时缓存TTL x3 */
#define CACHE_TTL_DEEP_IDLE_MULTIPLIER 5 /* 深度空闲时缓存TTL x5 */

/* ========== 日志定义 ========== */
#define LOG_I(fmt, ...) do { if (log_enabled) write_log("[I] " fmt, ##__VA_ARGS__); } while (0)
#define LOG_E(fmt, ...) do { if (log_enabled) write_log("[E] " fmt, ##__VA_ARGS__); } while (0)

/* ========== epoll/bitops宏 ========== */
#ifndef BITS_PER_LONG
#define BITS_PER_LONG (sizeof(long) * 8)
#endif
#define NBITS(x) ((((x) - 1) / BITS_PER_LONG) + 1)
#define test_bit(nr, addr) (((1UL << ((nr) % BITS_PER_LONG)) & (addr)[(nr) / BITS_PER_LONG]) != 0)

/* ========== 全局变量 ========== */
static int epfd = -1;
static int touch_fds[MAX_DEVICES];
static int touch_fd_count = 0;
static FILE* getevent_pipe = NULL;
static int getevent_fd = -1;
static bool log_enabled = false;
static FILE* log_fp = NULL;
static bool log_writing = false;
static char log_file_path[256] = {0};
static bool debug_set_from_args = false;

/* 前台应用缓存 */
static char cached_top_pkg[MAX_PKG_LEN] = {0};
static time_t last_top_pkg_time = 0;

/* 屏幕状态缓存 */
static bool screen_state_cached = true;
static time_t last_screen_check = 0;

/* 触摸检测模式切换 */
static bool use_getevent = false;

/* ========== 激进优化: inotify配置文件监控 ========== */
static int inotify_fd = -1;
static int inotify_watch_fd = -1;
static char config_path_buf[512] = {0};

/* ========== 激进优化: 自适应空闲检测 ========== */
static time_t last_global_touch_time = 0;  /* 全局最后触摸时间 */
static int adaptive_mode = 0; /* 0=normal, 1=idle, 2=deep_idle */

/* ========== AppConfig定义 ========== */
typedef struct {
    char package[MAX_PKG_LEN];
    long limit_time;
    time_t start_time;
    time_t last_touch_time;
    bool screen_off_triggered;
} AppConfig;

static AppConfig apps[MAX_APPS];
static int app_count = 0;
static time_t last_config_mtime = 0;

/* 日志节流变量 */
static time_t last_no_touch_log = 0;
static time_t last_cmd_fail_log = 0;
static time_t last_backlight_fail_log = 0;

/* 激进优化: 日志缓冲计数 */
static int log_flush_counter = 0;
#define LOG_FLUSH_INTERVAL 30  /* 每30秒强制flush一次 */

/* ========== 时间工具函数 ========== */
/* 激进优化: 使用clock_gettime(CLOCK_MONOTONIC)替代time(NULL)
 * 优势: 1. 不受NTP调整影响 2. 可能使用vDSO避免syscall开销 3. 单调递增保证定时器正确 */
static inline time_t get_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (time_t)ts.tv_sec;
}

static char* get_timestamp(void) {
    static char buf[32];
    time_t now = time(NULL);
    struct tm* tm = localtime(&now);
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", tm);
    return buf;
}

static void ensure_log_file(void) {
    if (!log_fp) {
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
        log_fp = fopen(log_file_path, "w");
        if (log_fp) fclose(log_fp);
        log_fp = NULL;
    }
}

/* 激进优化: 日志写入使用缓冲策略，减少磁盘I/O */
static void write_log(const char* fmt, ...) {
    ensure_log_file();
    if (!log_fp) return;
    check_log_size();
    if (!log_fp) {
        ensure_log_file();
        if (!log_fp) return;
    }
    log_writing = true;
    va_list args;
    va_start(args, fmt);
    fprintf(log_fp, "[%s] ", get_timestamp());
    vfprintf(log_fp, fmt, args);
    fprintf(log_fp, "\n");
    /* 激进优化: 不每次都fflush，减少磁盘I/O
     * 改为: 日志级别为E时立即flush，否则计数器达到阈值时flush */
    if (fmt[2] == 'E') {
        fflush(log_fp);  /* 错误日志立即落盘 */
    } else {
        log_flush_counter++;
        if (log_flush_counter >= LOG_FLUSH_INTERVAL) {
            fflush(log_fp);
            log_flush_counter = 0;
        }
    }
    va_end(args);
    log_writing = false;
}

/* 激进优化: 设置日志文件为全缓冲模式，减少syscall */
static void optimize_log_buffering(void) {
    if (log_fp) {
        char log_buf[4096];
        setvbuf(log_fp, log_buf, _IOFBF, sizeof(log_buf));
    }
}

/* ========== Fix1+Fix2: 重写exec_cmd函数 ========== */
/* Fix1: 修复fread循环中用strlen计算读取长度的缓冲区越界读取bug */
/* Fix2: 添加超时机制，防止dumpsys永久挂起导致程序永久阻塞 */
static int exec_cmd(const char* cmd, char* buf, size_t buf_size) {
    int pipefd[2];
    if (pipe(pipefd) < 0) {
        time_t now = get_now();
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("创建管道失败: %s", cmd);
            last_cmd_fail_log = now;
        }
        return -1;
    }
    pid_t pid = fork();
    if (pid == 0) {
        /* 子进程: 重定向stdout到管道写端 */
        close(pipefd[0]);
        dup2(pipefd[1], STDOUT_FILENO);
        close(pipefd[1]);
        execl("/system/bin/sh", "sh", "-c", cmd, NULL);
        _exit(127);
    }
    /* 父进程: 关闭管道写端 */
    close(pipefd[1]);
    /* 设置读取端为非阻塞 */
    int flags = fcntl(pipefd[0], F_GETFL, 0);
    fcntl(pipefd[0], F_SETFL, flags | O_NONBLOCK);
    /* 使用poll等待数据，带超时 */
    struct pollfd pfd;
    pfd.fd = pipefd[0];
    pfd.events = POLLIN;
    int poll_ret = poll(&pfd, 1, CMD_TIMEOUT_SEC * 1000);
    if (poll_ret == 0) {
        /* 超时 - 强制终止子进程 */
        kill(pid, SIGKILL);
        close(pipefd[0]);
        int status;
        waitpid(pid, &status, 0);
        if (buf) buf[0] = '\0';
        time_t now = get_now();
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("命令执行超时(%ds): %s", CMD_TIMEOUT_SEC, cmd);
            last_cmd_fail_log = now;
        }
        return -1;
    }
    if (poll_ret < 0) {
        close(pipefd[0]);
        int status;
        waitpid(pid, &status, 0);
        return -1;
    }
    /* Fix1: 使用fread返回值精确控制读取长度，不再使用strlen */
    size_t total_size = 0;
    if (buf) buf[0] = '\0';
    char read_buf[256];
    while (1) {
        pfd.revents = 0;
        int poll_ret2 = poll(&pfd, 1, 100); /* 每次读最多等100ms */
        if (poll_ret2 <= 0) break;
        ssize_t n = read(pipefd[0], read_buf, sizeof(read_buf));
        if (n <= 0) break;
        if (buf && total_size < buf_size - 1) {
            size_t space = buf_size - total_size - 1;
            if ((size_t)n > space) n = space;
            memcpy(buf + total_size, read_buf, n);
            total_size += n;
        }
    }
    if (buf) buf[total_size] = '\0';
    close(pipefd[0]);
    int status;
    waitpid(pid, &status, 0);
    return total_size > 0 || !buf ? 0 : -1;
}

/* ========== 激进优化: 自适应缓存TTL ========== */
/* 根据系统空闲状态动态调整缓存过期时间 */
static inline int get_top_pkg_cache_ttl(void) {
    if (adaptive_mode == 0) return 3;      /* 正常模式: 3秒 */
    if (adaptive_mode == 1) return 3 * CACHE_TTL_IDLE_MULTIPLIER;  /* 空闲: 9秒 */
    return 3 * CACHE_TTL_DEEP_IDLE_MULTIPLIER;  /* 深度空闲: 15秒 */
}

static inline int get_screen_check_interval(void) {
    if (adaptive_mode == 0) return 5;       /* 正常模式: 5秒 */
    if (adaptive_mode == 1) return 5 * CACHE_TTL_IDLE_MULTIPLIER;  /* 空闲: 15秒 */
    return 5 * CACHE_TTL_DEEP_IDLE_MULTIPLIER;  /* 深度空闲: 25秒 */
}

/* 激进优化: 更新自适应模式状态 */
static void update_adaptive_mode(time_t now) {
    time_t idle_time = now - last_global_touch_time;
    int new_mode = 0;
    if (idle_time >= IDLE_THRESHOLD_LONG) {
        new_mode = 2; /* 深度空闲 */
    } else if (idle_time >= IDLE_THRESHOLD_SHORT) {
        new_mode = 1; /* 空闲 */
    }
    if (new_mode != adaptive_mode) {
        const char* mode_names[] = {"正常", "空闲", "深度空闲"};
        LOG_I("自适应轮询模式切换: %s -> %s", mode_names[adaptive_mode], mode_names[new_mode]);
        adaptive_mode = new_mode;
    }
}

/* ========== get_top_app_name (激进优化: 自适应缓存 + 减少不必要调用) ========== */
static char* get_top_app_name(char* buf, size_t buf_size) {
    if (!buf || buf_size < MAX_PKG_LEN) {
        LOG_E("无效缓冲区或大小");
        return NULL;
    }
    time_t current_time = get_now();
    /* 激进优化: 使用自适应缓存TTL */
    if (current_time - last_top_pkg_time < get_top_pkg_cache_ttl() && cached_top_pkg[0]) {
        snprintf(buf, buf_size, "%s", cached_top_pkg);
        return buf;
    }
    char cmd_output[CMD_BUFFER_SIZE] = {0};
    const char* commands[] = {
        "/system/bin/dumpsys window | grep mCurrentFocus",
        "/system/bin/dumpsys window displays | grep -i mFocusedApp",
        "/system/bin/dumpsys activity activities",
        "/system/bin/dumpsys activity | grep -i mResumedActivity"
    };
    const char* keywords[] = {
        "mCurrentFocus=", "mFocusedApp=ActivityRecord{", "mActivityComponent=", "mResumedActivity:"
    };
    for (int i = 0; i < 4; i++) {
        if (exec_cmd(commands[i], cmd_output, sizeof(cmd_output)) == 0) {
            char* start = cmd_output;
            char* last_match = NULL;
            while ((start = strstr(start, keywords[i]))) {
                last_match = start;
                start += strlen(keywords[i]);
            }
            if (last_match) {
                start = last_match + strlen(keywords[i]);
                if (i == 0) {
                    while (*start && (*start == ' ' || *start == '{')) start++;
                    while (*start) {
                        if (*start == 'u' && isdigit(start[1])) {
                            start += 2;
                            while (isdigit(*start)) start++;
                            if (*start == ' ') start++;
                            break;
                        }
                        start++;
                    }
                } else if (i == 1) {
                    start = strchr(start, ' ');
                    if (start) {
                        start++;
                        while (*start && *start != ' ') start++;
                        start++;
                    }
                } else if (i == 3) {
                    start = strchr(start, '{');
                    if (start) {
                        start++;
                        while (*start && *start != ' ') start++;
                        if (*start == ' ') start++;
                        while (*start && *start != ' ') start++;
                        if (*start == ' ') start++;
                    }
                }
                if (*start) {
                    char* end = strchr(start, '/');
                    if (!end) end = strchr(start, ' ');
                    if (end) {
                        size_t len = end - start;
                        if (len < buf_size && len > 0) {
                            snprintf(buf, buf_size, "%.*s", (int)len, start);
                            snprintf(cached_top_pkg, sizeof(cached_top_pkg), "%s", buf);
                            last_top_pkg_time = current_time;
                            return buf;
                        }
                    }
                }
            }
        }
        memset(cmd_output, 0, sizeof(cmd_output));
    }
    buf[0] = '\0';
    return buf;
}

/* ========== Fix7: parse_time增加非法输入处理 ========== */
static long parse_time(const char* time_str) {
    long value = 0;
    char* endptr;
    value = strtol(time_str, &endptr, 10);
    if (value < 0) {
        LOG_E("无效的超时时间(负数): %s，使用默认值", time_str);
        return 15 * 60;  /* 返回默认15分钟 */
    }
    if (*endptr == 'h') return value * 3600;
    if (*endptr == 'm') return value * 60;
    if (*endptr == 's') return value;
    if (*endptr != '\0') {
        LOG_E("未知的超时时间后缀: %s，使用默认值", time_str);
    }
    return value * 60;  /* 无后缀默认按分钟处理（保持原有行为） */
}

/* ========== 触摸设备检测 ========== */
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
    if (epfd >= 0) return true;
    epfd = epoll_create1(0);
    if (epfd < 0) {
        return false;
    }
    if (!find_touch_devices()) {
        close(epfd);
        epfd = -1;
        use_getevent = true;
        return false;
    }
    struct epoll_event ev;
    for (int i = 0; i < touch_fd_count; i++) {
        ev.events = EPOLLIN;
        ev.data.fd = touch_fds[i];
        if (epoll_ctl(epfd, EPOLL_CTL_ADD, touch_fds[i], &ev) < 0) {
            for (int j = 0; j <= i; j++) close(touch_fds[j]);
            close(epfd);
            epfd = -1;
            touch_fd_count = 0;
            use_getevent = true;
            return false;
        }
    }
    return true;
}

/* Fix4: init_getevent增加epfd有效性检查 */
static bool init_getevent(void) {
    if (getevent_fd >= 0) return true;
    if (!getevent_pipe) {
        getevent_pipe = popen("getevent -q", "r");
        if (!getevent_pipe) {
            LOG_E("无法启动 getevent: %s", strerror(errno));
            return false;
        }
    }
    getevent_fd = fileno(getevent_pipe);
    int flags = fcntl(getevent_fd, F_GETFL, 0);
    fcntl(getevent_fd, F_SETFL, flags | O_NONBLOCK);
    /* Fix4: 如果epfd无效（-1），重新创建epoll实例 */
    if (epfd < 0) {
        epfd = epoll_create1(0);
        if (epfd < 0) {
            LOG_E("epoll_create1失败: %s", strerror(errno));
            pclose(getevent_pipe);
            getevent_pipe = NULL;
            getevent_fd = -1;
            return false;
        }
    }
    struct epoll_event ev;
    ev.events = EPOLLIN;
    ev.data.fd = getevent_fd;
    if (epoll_ctl(epfd, EPOLL_CTL_ADD, getevent_fd, &ev) < 0) {
        pclose(getevent_pipe);
        getevent_pipe = NULL;
        getevent_fd = -1;
        return false;
    }
    return true;
}

static void cleanup_touch_devices(void) {
    for (int i = 0; i < touch_fd_count; i++) {
        if (epfd >= 0) epoll_ctl(epfd, EPOLL_CTL_DEL, touch_fds[i], NULL);
        close(touch_fds[i]);
    }
    touch_fd_count = 0;
    if (getevent_fd >= 0) {
        if (epfd >= 0) epoll_ctl(epfd, EPOLL_CTL_DEL, getevent_fd, NULL);
        pclose(getevent_pipe);
        getevent_pipe = NULL;
        getevent_fd = -1;
    }
    if (epfd >= 0) {
        close(epfd);
        epfd = -1;
    }
}

/* ========== 激进优化: 自适应epoll超时 ========== */
static inline int get_adaptive_epoll_timeout(void) {
    if (adaptive_mode == 0) return TOUCH_CHECK_INTERVAL_NORMAL * 1000;    /* 5s */
    if (adaptive_mode == 1) return TOUCH_CHECK_INTERVAL_IDLE * 1000;      /* 10s */
    return TOUCH_CHECK_INTERVAL_DEEP_IDLE * 1000;                           /* 15s */
}

/* ========== check_touch_input (激进优化: 自适应超时 + 更新全局触摸时间) ========== */
static bool check_touch_input(time_t* last_touch) {
    if (touch_fd_count == 0 && !use_getevent && !init_touch_devices()) {
        use_getevent = true;
    }
    if (use_getevent && getevent_fd < 0 && !init_getevent()) {
        return false;
    }
    struct epoll_event events[MAX_DEVICES + 1];
    /* 激进优化: 使用自适应超时 */
    int timeout = get_adaptive_epoll_timeout();
    int nfds = epoll_wait(epfd, events, MAX_DEVICES + 1, timeout);
    if (nfds < 0) {
        if (errno == EINTR) return false;
        cleanup_touch_devices();
        use_getevent = true;
        return false;
    }
    if (nfds > 0) {
        bool touch_detected = false;
        for (int i = 0; i < nfds; i++) {
            int fd = events[i].data.fd;
            if (!use_getevent && fd != getevent_fd) {
                struct input_event ev;
                while (read(fd, &ev, sizeof(ev)) > 0) {
                    if (ev.type == EV_ABS && (
                        ev.code == ABS_MT_POSITION_X ||
                        ev.code == ABS_MT_POSITION_Y ||
                        ev.code == ABS_MT_TRACKING_ID ||
                        ev.code == ABS_MT_PRESSURE)) {
                        touch_detected = true;
                    } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH && ev.value == 1) {
                        touch_detected = true;
                    } else if (ev.type == EV_SYN && ev.code == SYN_REPORT) {
                        touch_detected = true;
                    }
                }
                if (errno != EAGAIN) {
                    cleanup_touch_devices();
                    use_getevent = true;
                    return false;
                }
            } else if (fd == getevent_fd) {
                static char buf[256];
                static size_t buf_pos = 0;
                ssize_t n;
                while ((n = read(fd, buf + buf_pos, sizeof(buf) - buf_pos - 1)) > 0) {
                    buf_pos += n;
                    buf[buf_pos] = '\0';
                    if (buf_pos > 0) {
                        touch_detected = true;
                        break;
                    }
                }
                if (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK) {
                    cleanup_touch_devices();
                    return false;
                }
            }
        }
        if (touch_detected) {
            *last_touch = get_now();
            /* 激进优化: 更新全局触摸时间，用于自适应模式切换 */
            last_global_touch_time = *last_touch;
            /* 检测到触摸时强制flush日志，确保用户操作被记录 */
            if (log_fp) fflush(log_fp);
            return true;
        }
    }
    return false;
}

/* ========== Fix3: is_screen_on背光分支降级逻辑修复 ========== */
/* 激进优化: 自适应缓存TTL */
static bool is_screen_on(void) {
    time_t now = get_now();
    /* 激进优化: 使用自适应缓存间隔 */
    int screen_check_interval = get_screen_check_interval();
    if (now - last_screen_check < screen_check_interval && last_screen_check != 0) {
        return screen_state_cached;
    }
    const char* backlight_path = "/sys/class/backlight/panel0-backlight/brightness";
    int fd = open(backlight_path, O_RDONLY);
    if (fd >= 0) {
        char buf[32] = {0};
        ssize_t n = read(fd, buf, sizeof(buf) - 1);
        close(fd);
        if (n > 0) {
            long value = strtol(buf, NULL, 10);
            if (value > 0) {
                char cmd_verify[512] = {0};
                if (exec_cmd("dumpsys display | grep mScreenState", cmd_verify, sizeof(cmd_verify)) == 0) {
                    screen_state_cached = (strstr(cmd_verify, "mScreenState=ON") != NULL);
                    last_screen_check = now;
                    return screen_state_cached;
                }
                /* Fix3: dumpsys验证失败时不直接返回false，继续走下面的降级检测 */
            } else {
                /* 亮度=0，屏幕确实关了 */
                screen_state_cached = false;
                last_screen_check = now;
                return screen_state_cached;
            }
        }
        /* 背光文件读取失败或value>0但dumpsys失败，fall through继续尝试其他方式 */
    }
    /* 继续尝试其他dumpsys检测方式 */
    char cmd_output[512] = {0};
    if (exec_cmd("dumpsys display | grep mScreenState", cmd_output, sizeof(cmd_output)) == 0) {
        screen_state_cached = (strstr(cmd_output, "mScreenState=ON") != NULL);
        last_screen_check = now;
        return screen_state_cached;
    }
    if (exec_cmd("dumpsys window | grep mScreenOn", cmd_output, sizeof(cmd_output)) == 0) {
        screen_state_cached = (strstr(cmd_output, "mScreenOnEarly=true") != NULL);
        last_screen_check = now;
        return screen_state_cached;
    }
    if (exec_cmd("dumpsys deviceidle get screen 2>/dev/null", cmd_output, sizeof(cmd_output)) == 0) {
        screen_state_cached = (strstr(cmd_output, "true") != NULL);
        last_screen_check = now;
        return screen_state_cached;
    }
    /* 所有检测方式都失败，保守返回true */
    screen_state_cached = true;
    last_screen_check = now;
    return true;
}

/* ========== trigger_screen_off (保持不变) ========== */
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
        if (!is_screen_on()) {
            app->screen_off_triggered = true;
            app->start_time = 0;
            app->last_touch_time = 0;
            LOG_I("应用 %s 无触控超时时限，触发屏幕息屏", app->package);
            return;
        }
    }
    LOG_E("无法触发屏幕息屏，请检查设备权限或背光文件路径");
}

/* ========== 激进优化: inotify配置文件监控 ========== */
/* 初始化inotify监控配置文件 */
static bool init_config_inotify(const char* config_path) {
    /* 复制配置路径 */
    strncpy(config_path_buf, config_path, sizeof(config_path_buf) - 1);
    config_path_buf[sizeof(config_path_buf) - 1] = '\0';

    inotify_fd = inotify_init();
    if (inotify_fd < 0) {
        LOG_E("inotify_init失败: %s，回退到stat轮询", strerror(errno));
        return false;
    }

    /* 监控文件的修改事件 */
    inotify_watch_fd = inotify_add_watch(inotify_fd, config_path_buf, IN_MODIFY | IN_CLOSE_WRITE);
    if (inotify_watch_fd < 0) {
        LOG_E("inotify_add_watch失败: %s，回退到stat轮询", strerror(errno));
        close(inotify_fd);
        inotify_fd = -1;
        return false;
    }

    LOG_I("配置文件inotify监控已启动: %s", config_path_buf);
    return true;
}

/* 激进优化: 检查inotify事件，如果有配置变更则重载 */
static bool check_config_inotify_event(void) {
    if (inotify_fd < 0) return false;

    char inotify_buf[512];
    ssize_t n = read(inotify_fd, inotify_buf, sizeof(inotify_buf));
    if (n > 0) {
        /* 解析inotify事件 */
        struct inotify_event* event = (struct inotify_event*)inotify_buf;
        if (event->mask & (IN_MODIFY | IN_CLOSE_WRITE)) {
            LOG_I("检测到配置文件变更，正在重载...");
            /* 加载新配置 */
            FILE* fp = fopen(config_path_buf, "r");
            if (fp) {
                /* 解析配置（复用load_config的逻辑但直接写入全局数组） */
                AppConfig temp_apps[MAX_APPS];
                int temp_app_count = 0;
                AppConfig* current_app = NULL;
                char line[CONFIG_LINE_MAX];
                while (fgets(line, sizeof(line), fp)) {
                    char* trimmed = line;
                    while (isspace(*trimmed)) trimmed++;
                    if (*trimmed == '\0' || *trimmed == '#') continue;
                    char* key = strtok(trimmed, "=");
                    char* value = strtok(NULL, "\n");
                    if (!key || !value) continue;
                    while (isspace(*key)) key++;
                    char* key_end = key + strlen(key) - 1;
                    while (key_end > key && isspace(*key_end)) {
                        *key_end = '\0';
                        key_end--;
                    }
                    while (isspace(*value)) value++;
                    if (strcmp(key, "package") == 0) {
                        if (temp_app_count < MAX_APPS) {
                            current_app = &temp_apps[temp_app_count++];
                            strncpy(current_app->package, value, MAX_PKG_LEN - 1);
                            current_app->package[MAX_PKG_LEN - 1] = '\0';
                            current_app->limit_time = 15 * 60;
                            current_app->start_time = 0;
                            current_app->last_touch_time = 0;
                            current_app->screen_off_triggered = false;
                            /* 保留已有跟踪状态 */
                            for (int i = 0; i < app_count; i++) {
                                if (strcmp(apps[i].package, current_app->package) == 0) {
                                    current_app->start_time = apps[i].start_time;
                                    current_app->last_touch_time = apps[i].last_touch_time;
                                    current_app->screen_off_triggered = apps[i].screen_off_triggered;
                                    break;
                                }
                            }
                        }
                    } else if (current_app && strcmp(key, "limit_time") == 0) {
                        current_app->limit_time = parse_time(value);
                    }
                }
                fclose(fp);
                memcpy(apps, temp_apps, sizeof(AppConfig) * temp_app_count);
                app_count = temp_app_count;
                LOG_I("配置文件重载完成，监控 %d 个应用", app_count);
            } else {
                LOG_E("重载配置文件失败: %s", strerror(errno));
            }
            return true;
        }
    }
    return false;
}

/* 激进优化: 清理inotify监控 */
static void cleanup_config_inotify(void) {
    if (inotify_fd >= 0) {
        if (inotify_watch_fd >= 0) {
            inotify_rm_watch(inotify_fd, inotify_watch_fd);
            inotify_watch_fd = -1;
        }
        close(inotify_fd);
        inotify_fd = -1;
    }
}

/* ========== 激进优化: 配置加载函数（提取为独立函数供inotify和启动时调用） ========== */
static int load_config_internal(const char* config_path) {
    FILE* fp = fopen(config_path, "r");
    if (!fp) {
        LOG_E("无法打开配置文件: %s", config_path);
        return -1;
    }
    AppConfig temp_apps[MAX_APPS];
    int temp_app_count = 0;
    AppConfig* current_app = NULL;
    char line[CONFIG_LINE_MAX];
    while (fgets(line, sizeof(line), fp)) {
        char* trimmed = line;
        while (isspace(*trimmed)) trimmed++;
        if (*trimmed == '\0' || *trimmed == '#') continue;
        char* key = strtok(trimmed, "=");
        char* value = strtok(NULL, "\n");
        if (!key || !value) continue;
        while (isspace(*key)) key++;
        /* Fix6: 去掉key尾部的空格 */
        char* key_end = key + strlen(key) - 1;
        while (key_end > key && isspace(*key_end)) {
            *key_end = '\0';
            key_end--;
        }
        while (isspace(*value)) value++;
        if (strcmp(key, "package") == 0) {
            if (temp_app_count < MAX_APPS) {
                current_app = &temp_apps[temp_app_count++];
                strncpy(current_app->package, value, MAX_PKG_LEN - 1);
                current_app->package[MAX_PKG_LEN - 1] = '\0';
                current_app->limit_time = 15 * 60;
                current_app->start_time = 0;
                current_app->last_touch_time = 0;
                current_app->screen_off_triggered = false;
                for (int i = 0; i < app_count; i++) {
                    if (strcmp(apps[i].package, current_app->package) == 0) {
                        current_app->start_time = apps[i].start_time;
                        current_app->last_touch_time = apps[i].last_touch_time;
                        current_app->screen_off_triggered = apps[i].screen_off_triggered;
                        break;
                    }
                }
            }
        } else if (current_app && strcmp(key, "limit_time") == 0) {
            current_app->limit_time = parse_time(value);
        }
    }
    fclose(fp);
    memcpy(apps, temp_apps, sizeof(AppConfig) * temp_app_count);
    app_count = temp_app_count;
    return 0;
}

/* 激进优化: 原load_config包装器（保持向后兼容） */
static int load_config(const char* config_path) {
    return load_config_internal(config_path);
}

/* ========== 激进优化: 设置进程优先级和I/O优先级 ========== */
static void set_process_priority(void) {
    /* 设置CPU优先级为最低(nice=19)，确保不抢占前台应用/CPU时间片 */
    if (setpriority(PRIO_PROCESS, 0, 19) < 0) {
        LOG_E("setpriority失败: %s", strerror(errno));
    } else {
        LOG_I("CPU优先级已设置为最低(nice=19)");
    }

    /* 尝试设置I/O优先级为idle类(类3)，让磁盘I/O只在系统空闲时执行 */
    /* 注意: ionice不是标准POSIX，Android可能不支持 */
    {
        /* 使用dlsym动态获取ionice函数，避免链接错误 */
        void* handle = dlopen("libc.so", RTLD_LAZY);
        if (handle) {
            typedef int (*ionice_fn)(int, int, int);
            ionice_fn ionice_fn_ptr = (ionice_fn)dlsym(handle, "ionice");
            if (ionice_fn_ptr) {
                if (ionice_fn_ptr(3, 0, 3) == 0) {  /* IOPRIO_CLASS_IDLE, priority 3 */
                    LOG_I("I/O优先级已设置为idle类");
                }
            }
            dlclose(handle);
        }
    }

    /* 设置进程名称便于识别 */
    prctl(PR_SET_NAME, "app_restrict", 0, 0, 0);
}

/* ========== main函数 ========== */
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
            debug_set_from_args = true;
        }
    }
    if (!config_path) {
        fprintf(stderr, "错误：必须提供 --config=<路径>\n");
        return 1;
    }
    if (log_file_path[0] && log_enabled) {
        ensure_log_file();
        if (!log_fp) {
            fprintf(stderr, "无法打开日志文件: %s\n", log_file_path);
            return 1;
        }
        /* 激进优化: 设置日志缓冲 */
        optimize_log_buffering();
    }
    if (load_config(config_path) != 0) {
        if (log_fp) fclose(log_fp);
        return 1;
    }
    if (app_count == 0) {
        LOG_E("配置文件中未找到有效应用");
        if (log_fp) fclose(log_fp);
        return 1;
    }
    LOG_I("启动应用时间限制守护进程（无触控息屏模式）");

    /* 激进优化: 设置进程优先级 */
    set_process_priority();

    /* 激进优化: 初始化inotify配置文件监控 */
    bool inotify_enabled = init_config_inotify(config_path);

    /* 初始化触摸设备 */
    init_touch_devices();

    /* 激进优化: 初始化全局触摸时间（避免启动时就被判定为空闲） */
    last_global_touch_time = get_now();

    time_t last_config_check = 0;  /* stat轮询备用（inotify失败时的fallback） */
    char current_app[MAX_PKG_LEN];
    bool last_logged_screen_state = true;

    /* ========== 激进优化: 自适应主循环 ========== */
    while (1) {
        time_t now = get_now();

        /* 激进优化: 更新自适应模式状态 */
        update_adaptive_mode(now);

        /* 屏幕状态检测（使用自适应缓存） */
        bool screen_on = is_screen_on();
        if (screen_on != last_logged_screen_state) {
            LOG_I("屏幕状态变为: %s", screen_on ? "开启" : "关闭");
            last_logged_screen_state = screen_on;
        }

        /* 屏幕关闭处理 */
        if (!screen_on) {
            for (int i = 0; i < app_count; i++) {
                if (apps[i].start_time != 0) {
                    apps[i].start_time = 0;
                    apps[i].last_touch_time = 0;
                    apps[i].screen_off_triggered = false;
                    LOG_I("屏幕关闭，停止跟踪 %s", apps[i].package);
                }
            }
            cleanup_touch_devices();
            sleep(SLEEP_INTERVAL_SCREEN_OFF);
            continue;
        }

        /* 激进优化: inotify检测配置变更（O(1)事件驱动，无轮询开销） */
        if (inotify_enabled) {
            if (check_config_inotify_event()) {
                /* 配置已重载，继续下一轮 */
                continue;
            }
        } else {
            /* Fallback: stat轮询（每10秒检查一次） */
            if (now - last_config_check >= 10) {
                struct stat st;
                if (stat(config_path, &st) == 0 && st.st_mtime > last_config_mtime) {
                    last_config_mtime = st.st_mtime;
                    load_config(config_path);
                    LOG_I("配置文件已更新，重新加载");
                }
                last_config_check = now;
            }
        }

        /* 触摸设备初始化（仅在需要时） */
        if (touch_fd_count == 0 && !use_getevent) {
            init_touch_devices();
        }

        /* 触摸检测（使用自适应超时） */
        bool has_touch = false;
        time_t last_touch = now;
        has_touch = check_touch_input(&last_touch);

        /* 激进优化: 当系统处于空闲/深度空闲模式且没有应用正在被跟踪时，
         * 跳过昂贵的get_top_app_name调用，减少fork+exec开销 */
        if (adaptive_mode == 0 || has_touch || app_count == 0) {
            /* 正常模式或检测到触摸或无应用时，检查前台应用 */
            if (get_top_app_name(current_app, sizeof(current_app))) {
                for (int i = 0; i < app_count; i++) {
                    AppConfig* app = &apps[i];
                    if (strcmp(current_app, app->package) == 0) {
                        if (app->start_time == 0) {
                            app->start_time = now;
                            app->last_touch_time = now;
                            app->screen_off_triggered = false;
                            LOG_I("开始跟踪 %s", app->package);
                        } else {
                            if (has_touch) {
                                app->last_touch_time = now;
                            }
                            if (now - app->last_touch_time >= app->limit_time &&
                                !app->screen_off_triggered) {
                                trigger_screen_off(app);
                            }
                        }
                    } else {
                        if (app->start_time != 0) {
                            app->start_time = 0;
                            app->last_touch_time = 0;
                            app->screen_off_triggered = false;
                            LOG_I("应用 %s 切换到后台，重置状态", app->package);
                        }
                    }
                }
            }
        } else {
            /* 空闲/深度空闲模式且无触摸: 跳过前台应用检测，
             * 但仍需检查是否有应用超时（使用缓存的前台应用名） */
            if (cached_top_pkg[0] && get_top_app_name(current_app, sizeof(current_app)) != NULL) {
                /* 仅在缓存前台应用与当前配置的应用匹配时才检查超时 */
                for (int i = 0; i < app_count; i++) {
                    AppConfig* app = &apps[i];
                    if (strcmp(current_app, app->package) == 0 && app->start_time != 0) {
                        if (now - app->last_touch_time >= app->limit_time &&
                            !app->screen_off_triggered) {
                            trigger_screen_off(app);
                        }
                    }
                }
            }
        }
    }

    /* 清理资源 */
    cleanup_config_inotify();
    cleanup_touch_devices();
    if (log_fp) fclose(log_fp);
    return 0;
}
