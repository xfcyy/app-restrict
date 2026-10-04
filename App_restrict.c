#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
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
#include <stdarg.h>
#include <signal.h>
#include <poll.h>
#include <sys/wait.h>

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

/* ========== 可配置参数(默认值，可通过配置文件覆盖) ========== */
/* cmd_timeout_ms: 单条外部命令硬超时(毫秒)，默认150，范围50-3000 */
static int cmd_timeout_ms = 150;
/* front_cache_sec: 前台应用名缓存有效期(秒)，默认300，范围3-3600 */
static int front_cache_sec = 300;
/* screen_check_sec: 屏幕状态检测间隔(秒)，默认10，范围1-300 */
static int screen_check_sec = 10;
/* max_poll_interval: 空闲轮询间隔上限(秒)，默认10，范围1-300 */
static int max_poll_interval = 10;
/* final_check_window_s: 到期前权威查询窗口(秒)，默认3，范围1-10 */
static int final_check_window_s = 3;
/* count_syn_report_as_touch: 诊断开关，1=SYN_REPORT算触摸(复现bug)，0=不算(修复后验证)，默认1 */
static int count_syn_report_as_touch = 1;

/* ========== 日志定义 ========== */
#define LOG_I(fmt, ...) do { if (log_enabled) write_log("[I] " fmt, ##__VA_ARGS__); } while (0)
#define LOG_E(fmt, ...) do { if (log_enabled) write_log("[E] " fmt, ##__VA_ARGS__); } while (0)
#define LOG_DIAG(fmt, ...) do { write_log("[DIAG] " fmt, ##__VA_ARGS__); } while (0)

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

/* 性能埋点统计 */
static int cmd_exec_count = 0;
static int cmd_timeout_count = 0;
static int cmd_slow_count = 0;
static long total_cmd_elapsed_ms = 0;
/* ========== 诊断埋点变量 ========== */
static int diag_event_log_count = 0;  /* 诊断原始事件日志计数器，硬限200行 */
#define DIAG_EVENT_LOG_MAX 200
static time_t last_diag_summary_time = 0;  /* 诊断汇总统计上次打印时间 */
static int diag_syn_report_count = 0;  /* 本周期SYN_REPORT计数 */
static int diag_abs_mt_count = 0;  /* 本周期ABS_MT_*计数 */
static int diag_btn_touch_count = 0;  /* 本周期BTN_TOUCH计数 */
static int diag_other_count = 0;  /* 本周期其他事件计数 */
static int diag_touch_judged_count = 0;  /* 本周期判定为触摸的次数 */
static int idle_spurious_count = 0;  /* 空闲期误触发触摸计数 */
static time_t last_real_touch_time = 0;  /* 上次真实触摸时间 */


/* ========== AppConfig定义(v6: bg_mismatch_count移入结构体，每应用独立) ========== */
typedef struct {
    char package[MAX_PKG_LEN];
    long limit_time;
    time_t start_time;
    time_t last_touch_time;
    bool screen_off_triggered;
    int bg_mismatch_count;  /* v6: 每应用独立的切换检测缓冲 */
} AppConfig;

static AppConfig apps[MAX_APPS];
static int app_count = 0;
static time_t last_config_mtime = 0;

/* 日志节流变量 */
static time_t last_no_touch_log = 0;
static time_t last_cmd_fail_log = 0;
static time_t last_backlight_fail_log = 0;
static time_t last_perf_log_time = 0;

/* v6: 每应用独立的切换缓冲阈值，提高到5次增加容错 */
#define BG_MISMATCH_THRESHOLD 5

/* ========== 时间工具函数 ========== */
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
    fflush(log_fp);
    va_end(args);
    log_writing = false;
}

/* ========== 性能埋点: 打印周期性能统计 ========== */
static void log_perf_stats(time_t now) {
    if (now - last_perf_log_time < 300) return; /* 每5分钟打印一次 */
    last_perf_log_time = now;
    if (cmd_exec_count > 0) {
        long avg_ms = total_cmd_elapsed_ms / cmd_exec_count;
        LOG_I("性能统计: 命令执行%d次, 超时%d次(%d%%), 慢命令%d次(%d%%), 平均耗时%ldms",
              cmd_exec_count, cmd_timeout_count,
              cmd_exec_count > 0 ? cmd_timeout_count * 100 / cmd_exec_count : 0,
              cmd_slow_count,
              cmd_exec_count > 0 ? cmd_slow_count * 100 / cmd_exec_count : 0,
              avg_ms);
    }
    /* 重置计数器 */
    cmd_exec_count = 0;
    cmd_timeout_count = 0;
    cmd_slow_count = 0;
    total_cmd_elapsed_ms = 0;
}

/* ========== exec_cmd(含性能埋点 + 可配超时) ========== */
static int exec_cmd(const char* cmd, char* buf, size_t buf_size) {
    struct timespec start_ts, end_ts;
    clock_gettime(CLOCK_MONOTONIC, &start_ts);
    
    cmd_exec_count++;
    
    int pipefd[2];
    if (pipe(pipefd) < 0) {
        time_t now = get_now();
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("创建管道失败: %s", cmd);
            last_cmd_fail_log = now;
        }
        clock_gettime(CLOCK_MONOTONIC, &end_ts);
        long elapsed = (end_ts.tv_sec - start_ts.tv_sec) * 1000 +
                       (end_ts.tv_nsec - start_ts.tv_nsec) / 1000000;
        total_cmd_elapsed_ms += elapsed;
        if (elapsed > 50) {
            cmd_slow_count++;
            LOG_E("命令执行耗时过长(%ldms): %s", elapsed, cmd);
        }
        return -1;
    }

    pid_t pid = fork();
    if (pid == 0) {
        close(pipefd[0]);
        dup2(pipefd[1], STDOUT_FILENO);
        close(pipefd[1]);
        execl("/system/bin/sh", "sh", "-c", cmd, NULL);
        _exit(127);
    }

    close(pipefd[1]);

    int flags = fcntl(pipefd[0], F_GETFL, 0);
    fcntl(pipefd[0], F_SETFL, flags | O_NONBLOCK);

    struct pollfd pfd;
    pfd.fd = pipefd[0];
    pfd.events = POLLIN;
    int poll_ret = poll(&pfd, 1, cmd_timeout_ms);

    if (poll_ret == 0) {
        kill(pid, SIGKILL);
        close(pipefd[0]);
        int status;
        waitpid(pid, &status, 0);
        if (buf) buf[0] = '\0';
        cmd_timeout_count++;
        time_t now = get_now();
        if (now - last_cmd_fail_log >= LOG_SUPPRESS_INTERVAL) {
            LOG_E("命令执行超时(%dms): %s", cmd_timeout_ms, cmd);
            last_cmd_fail_log = now;
        }
        clock_gettime(CLOCK_MONOTONIC, &end_ts);
        long elapsed = (end_ts.tv_sec - start_ts.tv_sec) * 1000 +
                       (end_ts.tv_nsec - start_ts.tv_nsec) / 1000000;
        total_cmd_elapsed_ms += elapsed;
        return -1;
    }

    if (poll_ret < 0) {
        close(pipefd[0]);
        int status;
        waitpid(pid, &status, 0);
        clock_gettime(CLOCK_MONOTONIC, &end_ts);
        long elapsed = (end_ts.tv_sec - start_ts.tv_sec) * 1000 +
                       (end_ts.tv_nsec - start_ts.tv_nsec) / 1000000;
        total_cmd_elapsed_ms += elapsed;
        return -1;
    }

    size_t total_size = 0;
    if (buf) buf[0] = '\0';
    char read_buf[256];

    while (1) {
        pfd.revents = 0;
        int poll_ret2 = poll(&pfd, 1, 100);
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
    
    clock_gettime(CLOCK_MONOTONIC, &end_ts);
    long elapsed = (end_ts.tv_sec - start_ts.tv_sec) * 1000 +
                   (end_ts.tv_nsec - start_ts.tv_nsec) / 1000000;
    total_cmd_elapsed_ms += elapsed;
    if (elapsed > 50) {
        cmd_slow_count++;
        LOG_E("命令执行耗时过长(%ldms): %s", elapsed, cmd);
    }
    
    return total_size > 0 || !buf ? 0 : -1;
}

/* ========== get_top_app_name(使用可配置缓存TTL) ========== */
static char* get_top_app_name(char* buf, size_t buf_size) {
    if (!buf || buf_size < MAX_PKG_LEN) {
        LOG_E("无效缓冲区或大小");
        return NULL;
    }
    time_t current_time = get_now();
    if (current_time - last_top_pkg_time < front_cache_sec && cached_top_pkg[0]) {
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

/* ========== parse_time增加非法输入处理 ========== */
static long parse_time(const char* time_str) {
    long value = 0;
    char* endptr;
    value = strtol(time_str, &endptr, 10);
    if (value < 0) {
        LOG_E("无效的超时时间(负数): %s，使用默认值", time_str);
        return 15 * 60;
    }
    if (*endptr == 'h') return value * 3600;
    if (*endptr == 'm') return value * 60;
    if (*endptr == 's') return value;
    if (*endptr != '\0') {
        LOG_E("未知的超时时间后缀: %s，使用默认值(按分钟解释)", time_str);
    }
    if (*endptr == '\0' && value > 0) {
        LOG_I("注意: limit_time=%ld 未指定后缀(s/m/h)，按分钟解释为%lds", value, value * 60);
    }
    return value * 60;
}

/* ========== v6: 去除字符串尾部空白字符(\r\n\t空格) ========== */
static void strip_trailing_whitespace(char* str) {
    char* end = str + strlen(str) - 1;
    while (end > str && isspace((unsigned char)*end)) {
        *end = '\0';
        end--;
    }
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

/* ========== check_touch_input(v6修复: 设备模式下SYN_REPORT不再单独触发触摸) ========== */
/* v6核心修复: SYN_REPORT是事件包同步标记，不是触摸动作本身。
 * 某些驱动在无触摸时也会周期性发送SYN_REPORT，导致last_touch_time被误更新，
 * 息屏计时器永远无法到期。v6改为：仅当SYN_REPORT伴随实际触摸数据(ABS_MT_POSITION_X等或BTN_TOUCH)时才计数。
 * 纯SYN_REPORT不再单独触发触摸标记。 */
static bool check_touch_input(time_t* last_touch) {
    if (touch_fd_count == 0 && !use_getevent && !init_touch_devices()) {
        use_getevent = true;
    }
    if (use_getevent && getevent_fd < 0 && !init_getevent()) {
        return false;
    }
    struct epoll_event events[MAX_DEVICES + 1];
    int timeout = max_poll_interval * 1000;
    int nfds = epoll_wait(epfd, events, MAX_DEVICES + 1, timeout);
    if (nfds < 0) {
        if (errno == EINTR) return false;
        cleanup_touch_devices();
        use_getevent = true;
        return false;
    }
    if (nfds > 0) {
        bool touch_detected = false;
        bool has_touch_data_this_frame = false;  /* v6: 跟踪本帧是否有真实触摸数据 */
        
        for (int i = 0; i < nfds; i++) {
            int fd = events[i].data.fd;
            if (!use_getevent && fd != getevent_fd) {
                struct input_event ev;
                while (read(fd, &ev, sizeof(ev)) > 0) {
                    /* 诊断: 记录事件类型用于统计 */
                    if (ev.type == EV_SYN && ev.code == SYN_REPORT) {
                        diag_syn_report_count++;
                    } else if (ev.type == EV_ABS && (
                        ev.code == ABS_MT_POSITION_X ||
                        ev.code == ABS_MT_POSITION_Y ||
                        ev.code == ABS_MT_TRACKING_ID ||
                        ev.code == ABS_MT_PRESSURE)) {
                        diag_abs_mt_count++;
                    } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH) {
                        diag_btn_touch_count++;
                    } else {
                        diag_other_count++;
                    }
                    /* 诊断: 打印原始事件(硬限200行) */
                    if (diag_event_log_count < DIAG_EVENT_LOG_MAX) {
                        const char* type_str = "UNKNOWN";
                        if (ev.type == EV_KEY) type_str = "EV_KEY";
                        else if (ev.type == EV_ABS) type_str = "EV_ABS";
                        else if (ev.type == EV_SYN) type_str = "EV_SYN";
                        else if (ev.type == EV_REL) type_str = "EV_REL";
                        LOG_DIAG("ev type=%d(%s) code=%d value=%d", ev.type, type_str, ev.code, ev.value);
                        diag_event_log_count++;
                    }
                    if (ev.type == EV_ABS && (
                        ev.code == ABS_MT_POSITION_X ||
                        ev.code == ABS_MT_POSITION_Y ||
                        ev.code == ABS_MT_TRACKING_ID ||
                        ev.code == ABS_MT_PRESSURE)) {
                        has_touch_data_this_frame = true;
                        touch_detected = true;
                    } else if (ev.type == EV_KEY && ev.code == BTN_TOUCH && ev.value == 1) {
                        has_touch_data_this_frame = true;
                        touch_detected = true;
                    } else if (ev.type == EV_SYN && ev.code == SYN_REPORT) {
                        /* v6修复: SYN_REPORT本身不是触摸，只有伴随真实触摸数据时才计数 */
                        if (has_touch_data_this_frame) {
                            touch_detected = true;
                        }
                        /* 诊断: SYN_REPORT单独出现时记录原因 */
                        if (!has_touch_data_this_frame && count_syn_report_as_touch) {
                            touch_detected = true;
                            LOG_DIAG("last_touch_time 更新 <- SYN_REPORT(空闲期误触发!)");
                        }
                    }
                }
                if (errno != EAGAIN) {
                    cleanup_touch_devices();
                    use_getevent = true;
                    return false;
                }
            } else if (fd == getevent_fd) {
                /* v5/v6: 正确解析getevent输出，只识别真正的触摸事件 */
                static char buf[2048];
                static size_t buf_pos = 0;
                ssize_t n;
                while ((n = read(fd, buf + buf_pos, sizeof(buf) - buf_pos - 1)) > 0) {
                    buf_pos += n;
                    buf[buf_pos] = '\0';
                    
                    char* line_start = buf;
                    char* line_end;
                    while ((line_end = strchr(line_start, '\n')) != NULL) {
                        *line_end = '\0';
                        
                        if (strstr(line_start, "ABS_MT_POSITION_X") ||
                            strstr(line_start, "ABS_MT_POSITION_Y") ||
                            strstr(line_start, "ABS_MT_TRACKING_ID") ||
                            strstr(line_start, "ABS_MT_PRESSURE") ||
                            strstr(line_start, "BTN_TOUCH")) {
                            touch_detected = true;
                        }
                        
                        line_start = line_end + 1;
                    }
                    if (*line_start != '\0') {
                        size_t remaining = strlen(line_start);
                        memmove(buf, line_start, remaining + 1);
                        buf_pos = remaining;
                    } else {
                        buf_pos = 0;
                    }
                }
                if (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK) {
                    cleanup_touch_devices();
                    return false;
                }
            }
        }
        if (touch_detected) {
            diag_touch_judged_count++;
            *last_touch = get_now();
            /* 诊断: 记录last_touch_time更新原因 */
            if (diag_event_log_count >= DIAG_EVENT_LOG_MAX && get_now() - last_real_touch_time > 2) {
                idle_spurious_count++;
                if (idle_spurious_count % 10 == 1) {
                    LOG_DIAG("last_touch_time 更新 <- 事件判定(空闲期误触发! idle_spurious=%d)", idle_spurious_count);
                }
            }
            last_real_touch_time = *last_touch;
            return true;
        }
    }
    /* 诊断: 周期性打印事件统计汇总 */
    if (get_now() - last_diag_summary_time >= 1) {
        last_diag_summary_time = get_now();
        LOG_DIAG("[DIAG统计] 本秒事件总数=%d | SYN_REPORT=%d | ABS_MT_POSITION_X/Y=%d | BTN_TOUCH=%d | 其他=%d | 判定触摸=%d",
                 diag_syn_report_count + diag_abs_mt_count + diag_btn_touch_count + diag_other_count,
                 diag_syn_report_count, diag_abs_mt_count, diag_btn_touch_count, diag_other_count,
                 diag_touch_judged_count);
        if (idle_spurious_count > 0) {
            LOG_DIAG("[DIAG] idle_spurious_count=%d (空闲期误触发触摸次数)", idle_spurious_count);
        }
        /* 重置本周期计数器 */
        diag_syn_report_count = 0;
        diag_abs_mt_count = 0;
        diag_btn_touch_count = 0;
        diag_other_count = 0;
        diag_touch_judged_count = 0;
    }
    return false;
}

/* ========== is_screen_on(纯sysfs实现) ========== */
static bool is_screen_on(void) {
    time_t now = get_now();
    if (now - last_screen_check < screen_check_sec && last_screen_check != 0) {
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
            screen_state_cached = (value > 0);
            last_screen_check = now;
            return screen_state_cached;
        }
        screen_state_cached = true;
        last_screen_check = now;
        return true;
    }
    screen_state_cached = true;
    last_screen_check = now;
    return true;
}

/* ========== trigger_screen_off(保持不变) ========== */
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

/* ========== 配置文件加载(v6修复: package值尾部\r清除 + 所有值尾部空白清除) ========== */
static int load_config(const char* config_path) {
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
        /* 去掉key尾部的空格 */
        char* key_end = key + strlen(key) - 1;
        while (key_end > key && isspace(*key_end)) {
            *key_end = '\0';
            key_end--;
        }
        while (isspace(*value)) value++;
        
        /* v6修复: 去除value尾部的\r\n等空白字符(解决Windows/CRLF配置文件包名匹配失败) */
        strip_trailing_whitespace(value);
        
        if (strcmp(key, "package") == 0) {
            if (temp_app_count < MAX_APPS) {
                current_app = &temp_apps[temp_app_count++];
                strncpy(current_app->package, value, MAX_PKG_LEN - 1);
                current_app->package[MAX_PKG_LEN - 1] = '\0';
                current_app->limit_time = 15 * 60;
                current_app->start_time = 0;
                current_app->last_touch_time = 0;
                current_app->screen_off_triggered = false;
                current_app->bg_mismatch_count = 0;
                /* 热重载时保留运行状态 */
                for (int i = 0; i < app_count; i++) {
                    if (strcmp(apps[i].package, current_app->package) == 0) {
                        current_app->start_time = apps[i].start_time;
                        current_app->last_touch_time = apps[i].last_touch_time;
                        current_app->screen_off_triggered = apps[i].screen_off_triggered;
                        current_app->bg_mismatch_count = apps[i].bg_mismatch_count;
                        break;
                    }
                }
            }
        } else if (strcmp(key, "limit_time") == 0) {
            if (!current_app) {
                LOG_E("配置文件错误: limit_time 出现在 package 之前，已忽略");
            } else {
                current_app->limit_time = parse_time(value);
                LOG_I("配置更新: limit_time=%ld", current_app->limit_time);
            }
        } else if (strcmp(key, "cmd_timeout_ms") == 0) {
            long val = strtol(value, NULL, 10);
            if (val < 50) val = 50;
            if (val > 3000) val = 3000;
            cmd_timeout_ms = (int)val;
            LOG_I("配置更新: cmd_timeout_ms=%d", cmd_timeout_ms);
        } else if (strcmp(key, "front_cache_sec") == 0) {
            long val = strtol(value, NULL, 10);
            if (val < 3) val = 3;
            if (val > 3600) val = 3600;
            front_cache_sec = (int)val;
            LOG_I("配置更新: front_cache_sec=%d", front_cache_sec);
        } else if (strcmp(key, "screen_check_sec") == 0) {
            long val = strtol(value, NULL, 10);
            if (val < 1) val = 1;
            if (val > 300) val = 300;
            screen_check_sec = (int)val;
            LOG_I("配置更新: screen_check_sec=%d", screen_check_sec);
        } else if (strcmp(key, "max_poll_interval") == 0) {
            long val = strtol(value, NULL, 10);
            if (val < 1) val = 1;
            if (val > 300) val = 300;
            max_poll_interval = (int)val;
            LOG_I("配置更新: max_poll_interval=%d", max_poll_interval);
        } else if (strcmp(key, "final_check_window_s") == 0) {
            long val = strtol(value, NULL, 10);
            if (val < 1) val = 1;
            if (val > 10) val = 10;
            final_check_window_s = (int)val;
            LOG_I("配置更新: final_check_window_s=%d", final_check_window_s);
        } else if (strcmp(key, "count_syn_report_as_touch") == 0) {
            long val = strtol(value, NULL, 10);
            if (val < 0) val = 0;
            if (val > 1) val = 1;
            count_syn_report_as_touch = (int)val;
            LOG_I("配置更新: count_syn_report_as_touch=%d", count_syn_report_as_touch);
        }
    }
    fclose(fp);
    memcpy(apps, temp_apps, sizeof(AppConfig) * temp_app_count);
    app_count = temp_app_count;
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

/* ========== main函数(v6: 日志节流 + 每应用独立缓冲 + 10ms休眠) ========== */
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
    LOG_I("参数: cmd_timeout=%dms, front_cache=%ds, screen_check=%ds, poll_interval=%ds",
          cmd_timeout_ms, front_cache_sec, screen_check_sec, max_poll_interval);
    /* v6: 启动时打印每个应用的完整配置 */
    for (int idx = 0; idx < app_count; idx++) {
        LOG_I("应用配置[%d]: package=%s, limit_time=%lds(%d分钟)", idx, 
              apps[idx].package, apps[idx].limit_time, (int)(apps[idx].limit_time / 60));
    }
    LOG_I("提示: 日志已节流(仅应用变化时打印)，主循环已添加10ms休眠以减少系统负载");
    if (count_syn_report_as_touch) {
        LOG_I("[DIAG] 诊断模式已启用: count_syn_report_as_touch=1 (SYN_REPORT将计入触摸)");
    }
    
    init_touch_devices();
    time_t last_config_check = 0;
    char current_app[MAX_PKG_LEN];
    bool last_logged_screen_state = true;
    
    /* v6: 日志节流 - 仅在前台应用变化时打印 */
    static char last_logged_app[MAX_PKG_LEN] = {0};
    
    while (1) {
        time_t now = get_now();
        
        /* 定期打印性能统计 */
        log_perf_stats(now);
        
        /* 屏幕状态检测（使用纯sysfs，零fork） */
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
        
        /* 配置文件热重载检测 */
        if (now - last_config_check >= 10) {
            if (check_config_updated(config_path)) {
                load_config(config_path);
            }
            last_config_check = now;
        }
        
        /* 触摸设备初始化（仅在需要时） */
        if (touch_fd_count == 0 && !use_getevent) {
            init_touch_devices();
        }
        
        /* 触摸检测（使用可配置超时） */
        bool has_touch = false;
        time_t last_touch = now;
        has_touch = check_touch_input(&last_touch);
        
        /* 前台应用检测 + 应用跟踪逻辑 */
        get_top_app_name(current_app, sizeof(current_app));
        
        /* 空检测不重置状态 */
        if (current_app[0] == '\0') {
            /* v6: 无法检测前台应用时，重置所有应用的切换缓冲计数器 */
            for (int _k = 0; _k < app_count; _k++) {
                apps[_k].bg_mismatch_count = 0;
            }
            sleep(1);
            continue;
        }
        
        /* v6修复: 日志节流 - 仅在前台应用变化时打印 */
        if (strcmp(current_app, last_logged_app) != 0) {
            strncpy(last_logged_app, current_app, sizeof(last_logged_app) - 1);
            last_logged_app[sizeof(last_logged_app) - 1] = '\0';
            LOG_I("检测到前台应用: %s", current_app);
        }
        
        for (int i = 0; i < app_count; i++) {
            AppConfig* app = &apps[i];
            if (strcmp(current_app, app->package) == 0) {
                /* 匹配到目标应用 */
                app->bg_mismatch_count = 0;  /* v6: 使用 per-app 计数器 */
                if (app->start_time == 0) {
                    app->start_time = now;
                    app->last_touch_time = now;
                    app->screen_off_triggered = false;
                    LOG_DIAG("状态迁移: IDLE -> TRACKING (应用=%s, 剩余=%lds)", app->package, app->limit_time);
                    LOG_I("开始跟踪 %s", app->package);
                } else {
                    if (has_touch) {
                        app->last_touch_time = now;
                    }
                    if (now - app->last_touch_time >= app->limit_time &&
                        !app->screen_off_triggered) {
                        LOG_DIAG("状态迁移: TRACKING -> SCREEN_OFF (应用=%s)", app->package);
                        LOG_DIAG("权威查询命中，触发息屏");
                        trigger_screen_off(app);
                    }
                }
            } else {
                /* v6修复: 使用 per-app 缓冲计数器，防止偶发检测失败导致误重置 */
                if (app->start_time != 0) {
                    app->bg_mismatch_count++;
                    if (app->bg_mismatch_count >= BG_MISMATCH_THRESHOLD) {
                        app->start_time = 0;
                        app->last_touch_time = 0;
                        app->screen_off_triggered = false;
                        app->bg_mismatch_count = 0;
                        LOG_DIAG("状态迁移: TRACKING -> IDLE (原因=应用切后台, 不匹配次数=%d)", app->bg_mismatch_count);
                        LOG_I("应用 %s 切换到后台，重置状态(第%d次不匹配)", app->package, app->bg_mismatch_count);
                    }
                }
            }
        }
        
        /* v6修复: 主循环末尾10ms休眠，降低CPU占用和磁盘I/O竞争 */
        usleep(10000);
    }
    
    cleanup_touch_devices();
    if (log_fp) fclose(log_fp);
    return 0;
}
