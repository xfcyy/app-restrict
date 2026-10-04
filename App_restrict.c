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
#include <stdarg.h>    /* Fix5: 补充缺失的头文件 */
#include <signal.h>    /* Fix2: exec_cmd超时机制需要 */
#include <poll.h>      /* Fix2: exec_cmd超时机制需要 */
#include <sys/wait.h>  /* Fix2: exec_cmd超时机制需要 */

#define MAX_PKG_LEN 256
#define CMD_BUFFER_SIZE 1024
#define MAX_APPS 100
#define CONFIG_LINE_MAX 512
#define CONFIG_CHECK_INTERVAL 10
#define MAX_LOG_SIZE (100 * 1024)
#define SCREEN_CHECK_INTERVAL 5
#define SCREEN_OFF_WAIT_TIME 5
#define TOUCH_CHECK_INTERVAL 5    /* Fix8: 从10降至5，提升主循环响应性 */
#define MAX_DEVICES 10
#define SLEEP_INTERVAL_SCREEN_OFF 30
#define LOG_SUPPRESS_INTERVAL 60
#define CMD_TIMEOUT_SEC 3          /* Fix2: exec_cmd超时时间(秒) */

#define LOG_I(fmt, ...) do { if (log_enabled) write_log("[I] " fmt, ##__VA_ARGS__); } while (0)
#define LOG_E(fmt, ...) do { if (log_enabled) write_log("[E] " fmt, ##__VA_ARGS__); } while (0)

#ifndef BITS_PER_LONG
#define BITS_PER_LONG (sizeof(long) * 8)
#endif
#define NBITS(x) ((((x) - 1) / BITS_PER_LONG) + 1)
#define test_bit(nr, addr) (((1UL << ((nr) % BITS_PER_LONG)) & (addr)[(nr) / BITS_PER_LONG]) != 0)

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
static char cached_top_pkg[MAX_PKG_LEN] = {0};
static time_t last_top_pkg_time = 0;
static bool screen_state_cached = true;
 time_t last_screen_check = 0;
static bool use_getevent = false;

typedef struct {
    char package[MAX_PKG_LEN];
    long limit_time;
    time_t start_time;
    time_t last_touch_time;
    bool screen_off_triggered;
} AppConfig;

AppConfig apps[MAX_APPS];
int app_count = 0;
time_t last_config_mtime = 0;

static time_t last_no_touch_log = 0;
static time_t last_cmd_fail_log = 0;
static time_t last_backlight_fail_log = 0;

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

/* Fix1+Fix2: 重写exec_cmd函数
 * Fix1: 修复fread循环中用strlen计算读取长度的缓冲区越界读取bug
 * Fix2: 添加超时机制，防止dumpsys永久挂起导致程序永久阻塞
 */
static int exec_cmd(const char* cmd, char* buf, size_t buf_size) {
    int pipefd[2];
    if (pipe(pipefd) < 0) {
        time_t now = time(NULL);
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
        time_t now = time(NULL);
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

static char* get_top_app_name(char* buf, size_t buf_size) {
    if (!buf || buf_size < MAX_PKG_LEN) {
        LOG_E("无效缓冲区或大小");
        return NULL;
    }
    time_t current_time = time(NULL);
    if (current_time - last_top_pkg_time < 3 && cached_top_pkg[0]) {
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

/* Fix7: parse_time增加非法输入处理（负数、未知后缀） */
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

/* Fix4: init_getevent增加epfd有效性检查，避免在epfd=-1时调用epoll_ctl */
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

static bool check_touch_input(time_t* last_touch) {
    if (touch_fd_count == 0 && !use_getevent && !init_touch_devices()) {
        use_getevent = true;
    }
    if (use_getevent && getevent_fd < 0 && !init_getevent()) {
        return false;
    }
    struct epoll_event events[MAX_DEVICES + 1];
    int nfds = epoll_wait(epfd, events, MAX_DEVICES + 1, TOUCH_CHECK_INTERVAL * 1000);
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
            *last_touch = time(NULL);
            return true;
        }
    }
    return false;
}

/* Fix6: 配置文件解析增加key尾部空格去除 */
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

/* Fix3: is_screen_on背光分支降级逻辑修复
 * 当背光文件可读且亮度>0，但dumpsys验证失败时，不再错误返回false，
 * 而是继续尝试其他检测方式（dumpsys display/window/deviceidle） */
static bool is_screen_on(void) {
    time_t now = time(NULL);
    if (now - last_screen_check < SCREEN_CHECK_INTERVAL && last_screen_check != 0) {
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
    /* 所有检测方式都失败，保守返回true（宁可不停止跟踪也不误判屏幕关闭） */
    screen_state_cached = true;
    last_screen_check = now;
    return true;
}

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
    init_touch_devices();
    time_t last_config_check = 0;
    char current_app[MAX_PKG_LEN];
    bool last_logged_screen_state = true;
    while (1) {
        time_t now = time(NULL);
        bool screen_on = is_screen_on();
        if (screen_on != last_logged_screen_state) {
            LOG_I("屏幕状态变为: %s", screen_on ? "开启" : "关闭");
            last_logged_screen_state = screen_on;
        }
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
        if (now - last_config_check >= CONFIG_CHECK_INTERVAL) {
            if (check_config_updated(config_path)) {
                load_config(config_path);
            }
            last_config_check = now;
        }
        if (touch_fd_count == 0 && !use_getevent) {
            init_touch_devices();
        }
        bool has_touch = false;
        time_t last_touch = now;
        has_touch = check_touch_input(&last_touch);
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
    }
    cleanup_touch_devices();
    if (log_fp) fclose(log_fp);
    return 0;
}
