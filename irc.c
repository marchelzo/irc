#define _GNU_SOURCE

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdnoreturn.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <errno.h>
#include <ctype.h>
#include <assert.h>

#include <unistd.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <signal.h>
#include <pthread.h>

#include <tickit.h>

#include "utf8.h"

static void command_join(char *);
static void command_raw(char *);
static void command_msg(char *);
static void command_action(char *);
static void command_part(char *);
static void command_quit(char *);
static void command_here(char *);
static void command_topic(char *);

static void irc_privmsg(char *, char *, char *);
static void run_command(char const *, char *);

enum irc_reply_type {
    IRC_ERROR,
    IRC_JOIN,
    IRC_MODE,
    IRC_MOTD,
    IRC_MOTD_END,
    IRC_MOTD_START,
    IRC_NAMES,
    IRC_NAMES_END,
    IRC_NEED_MORE_PARAMS,
    IRC_NOTICE,
    IRC_NOT_IMPLEMENTED,
    IRC_PART,
    IRC_PING,
    IRC_PRIVMSG,
    IRC_QUIT,
    IRC_TOPIC,
    IRC_TOPIC_WHO_TIME,
    IRC_UNKNOWN_COMMAND,
    IRC_WELCOME
};

struct irc_reply {
    enum irc_reply_type type;
    struct {
        enum { IRC_PREFIX_SERVER, IRC_PREFIX_USER } type;
        union {
            char *server;
            struct {
                char *nick;
                char *user;
                char *host;
            };
        };
    } prefix;
    bool has_prefix;
    size_t paramc;
    char **paramv;
};

struct nick_node {
    char *nick;
    struct nick_node *next;
};

struct nick_list {
    size_t count;
    struct nick_node *head;
};

struct room {
    enum { ROOM_PRIVATE, ROOM_CHANNEL, ROOM_SERVER } type;
    char *target;
    char *topic;
    struct nick_list nicks;
    atomic_uchar activity;
};

struct message {
    enum { MSG_NORMAL, MSG_NOTIFICATION, MSG_SERVER, MSG_ACTION, MSG_WARNING } type;
    time_t timestamp;
    char *target;
    char *from;
    char *text;
};

struct color {
    unsigned char fg;
    unsigned char bg;
};

typedef void (*command_function)(char *);
struct { char const *name; command_function function; } command_table[] = {
    { "join",  command_join    },
    { "raw",   command_raw     },
    { "msg",   command_msg     },
    { "me",    command_action  },
    { "part",  command_part    },
    { "quit",  command_quit    },
    { "here",  command_here    },
    { "topic", command_topic   }
};

static size_t const command_count = sizeof command_table / sizeof command_table[0];

struct { char const *string; enum irc_reply_type type; } irc_reply_table[] = {
    { "372",     IRC_MOTD             },
    { "ERROR",   IRC_ERROR            },
    { "NOTICE",  IRC_NOTICE           },
    { "PART",    IRC_PART             },
    { "PRIVMSG", IRC_PRIVMSG          },
    { "375",     IRC_MOTD_START       },
    { "376",     IRC_MOTD_END         },
    { "PING",    IRC_PING             },
    { "461",     IRC_NEED_MORE_PARAMS },
    { "421",     IRC_UNKNOWN_COMMAND  },
    { "353",     IRC_NAMES            },
    { "366",     IRC_NAMES_END        },
    { "001",     IRC_WELCOME          },
    { "MODE",    IRC_MODE             },
    { "QUIT",    IRC_QUIT             },
    { "JOIN",    IRC_JOIN             },
    { "332",     IRC_TOPIC            },
    { "333",     IRC_TOPIC_WHO_TIME   }
};

static size_t const irc_replies = sizeof irc_reply_table / sizeof irc_reply_table[0];

static struct nick_list const empty_nick_list = { 0, NULL };

enum {
    ACTIVITY_NONE      = 0,
    ACTIVITY_NORMAL    = 1,
    ACTIVITY_IMPORTANT = 2
};

static struct {
    struct color
        input,
        normal,
        warning,
        notification,
        timestamp,
        my_nick,
        nick,
        nick_mentioned,
        action,
        activity,
        important_activity ;
} colors = {
    {230, 237},
    {230, 0},
    {31,  0},
    {241, 0},
    {237, 0},
    {62,  0},
    {107, 0},
    {172, 0},
    {192, 0},
    {165, 0},
    {14,  0}
};

static int connection = -1;

static char *flag_network = "irc.freenode.net";
static char *port;
static struct {
    char *nick;
    char *username;
    char *real_name;
    char *auth_string;
} user;

static bool flag_no_sasl;
static bool flag_no_handler;

static int nicklength = 16;
static bool autoswitch = true;

static int ext_handler_pid = -1;
static int ext_handler_fd = -1;

static size_t autojoin_count;
static char *autojoin[10];

static size_t cursor_bytes;
static size_t input_idx;
static size_t input_count;
static char *input_keys[1024];
static char input_buffer[4096];

static pthread_t listener_thread;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

static int rows;
static int columns;

static size_t scroll_idx;

static struct message *messages;
static size_t message_count;
static size_t message_alloc;

static struct room *room;
static struct room *rooms;
static size_t room_count;
static size_t room_alloc;

static atomic_bool should_render_input_line = true;
static atomic_bool should_render_messages = true;
static atomic_bool should_render_status = true;
static atomic_bool should_pong;

static TickitTerm *t;
static TickitPen *default_pen;

static struct {
    TickitWindow *root;
    TickitWindow *messages;
    TickitWindow *input;
    TickitWindow *status;
} windows;

static FILE *log_file;

static void cleanup(void)
{
    if (ext_handler_pid != -1)
        kill(ext_handler_pid, SIGKILL);

    pthread_cancel(listener_thread);

    if (connection != -1 && write(connection, "goodbye", 7) != -1)
        shutdown(connection, SHUT_RDWR);

    if (t) {
        tickit_term_clear(t);
        tickit_term_flush(t);
        tickit_term_setctl_int(t, TICKIT_TERMCTL_MOUSE, TICKIT_TERM_MOUSEMODE_OFF);
        tickit_term_destroy(t);
    }
}

static void sigint(int _)
{
        exit(EXIT_SUCCESS);
}

static void record(char const *fmt, ...)
{
#ifdef DEBUG
    va_list ap;
    va_start(ap, fmt);
    vfprintf(log_file, fmt, ap);
    va_end(ap);
    fflush(log_file);
#endif
}

noreturn static void fatal(char const *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fputs("Error: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);

    exit(EXIT_FAILURE);
}

static char const *irc_str_type(struct irc_reply const *msg)
{
    for (size_t i = 0; i < irc_replies; ++i) {
        if (msg->type == irc_reply_table[i].type) {
            return irc_reply_table[i].string;
        }
    }

    return NULL;
}

static char *duplicate(char const *s)
{
    size_t length = strlen(s);
    char *result = malloc(length + 1);

    if (!result)
        fatal("Out of memory...");

    char *r = result;
    for (size_t i = 0; i <= length; ++i)
        if (s[i] > 10 || s[i] <= 1)
            *r++ = s[i];

    return result;
}

static bool contains_nick(char const *s)
{
    char *n = strstr(s, user.nick);

    if (!n)
        return false;

    if (n != s && isalnum(n[-1]))
        return false;

    if (isalnum(n[strlen(user.nick)]))
        return false;
    
    return true;
}

static void irc_write_json(struct irc_reply const *msg, int fd)
{
    write(fd, "{", 1);

    write(fd, "\"type\":", 7);
    char const *type = irc_str_type(msg);
    if (type) {
        write(fd, "\"", 1);
        write(fd, type, strlen(type));
        write(fd, "\"", 1);
    } else {
        write(fd, "null", 4);
    }

    write(fd, ",", 1);

    write(fd, "\"nick\":", 7);
    if (msg->prefix.nick) {
        write(fd, "\"", 1);
        write(fd, msg->prefix.nick, strlen(msg->prefix.nick));
        write(fd, "\"", 1);
    } else {
        write(fd, "null", 4);
    }

    write(fd, ",", 1);

    write(fd, "\"user\":", 7);
    if (msg->prefix.user) {
        write(fd, "\"", 1);
        write(fd, msg->prefix.user, strlen(msg->prefix.user));
        write(fd, "\"", 1);
    } else {
        write(fd, "null", 4);
    }

    write(fd, ",", 1);

    write(fd, "\"host\":", 7);
    if (msg->prefix.host) {
        write(fd, "\"", 1);
        write(fd, msg->prefix.host, strlen(msg->prefix.host));
        write(fd, "\"", 1);
    } else {
        write(fd, "null", 4);
    }

    write(fd, ",", 1);

    write(fd, "\"params\":[", 10);
    for (size_t i = 0; i < msg->paramc; ++i) {
        char const *param = msg->paramv[i];
        write(fd, "\"", 1);
        while (*param) {
            if (*param == '\\')
                write(fd, "\\\\", 2);
            else if (*param == '"')
                write(fd, "\\\"", 2);
            else
                write(fd, param, 1);

            param += 1;
        }
        write(fd, "\"", 1);

        if (i + 1 == msg->paramc)
            write(fd, "]", 1);
        else
            write(fd, ",", 1);
    }

    write(fd, "}", 1);

    write(fd, "\n", 1);
}

static void load_handler(char const *s)
{
    char type[32];
    char handler[256];
    char *hp;

    if (flag_no_handler)
        return;

    if (sscanf(s, "%31s = %255s", type, handler) == 2) {
        if (!strcmp(type, "handler")) {
            hp = duplicate(handler);
            hp[strcspn(hp, "\n")] = 0;

            errno = 0;
            int p[2];
            pipe(p);

            if (errno)
                fatal("Failed pipe: %s\n", strerror(errno));            


            int pid;
            if (!(pid = fork())) {
                errno = 0;

                dup2(p[0], STDIN_FILENO);

                if (errno)
                        fatal("Failed dup2: %s\n", strerror(errno));            

                close(STDOUT_FILENO);
                if (errno)
                        fatal("Failed to close STDOUT_FILENO: %s\n", strerror(errno));            

                open("/dev/null", O_WRONLY);
                if (errno)
                        fatal("Failed to open /dev/null: %s\n", strerror(errno));            

                execlp(hp, hp, NULL);

                if (errno)
                        fatal("Failed execvp: %s\n", strerror(errno));            
            } else {
                close(p[0]);
                ext_handler_fd = p[1];
                ext_handler_pid = pid;
                return;
            }
        }
    }

    fatal("Invalid setting in the handler section of the "\
          "configuration file: `%s`", s);
}

static void load_color(char const *s)
{
    char element[32];
    char fg[32];
    char bg[32];

    if (sscanf(s, "%31s = %31s %31s", element, fg, bg) == 3) {
        char *end;
        long fg_value = strtol(fg, &end, 10);
        if (*end)
            goto error;
        long bg_value = strtol(bg, &end, 10);
        if (*end)
            goto error;

        if (fg_value < 0 || fg_value > 255 || bg_value < 0 || bg_value > 255)
            goto error;

        struct color c = (struct color){fg_value, bg_value};
        if (!strcmp(element, "input"))
            colors.input = c;
        else if (!strcmp(element, "normal"))
            colors.normal = c;
        else if (!strcmp(element, "warning"))
            colors.warning = c;
        else if (!strcmp(element, "notification"))
            colors.notification = c;
        else if (!strcmp(element, "timestamp"))
            colors.timestamp = c;
        else if (!strcmp(element, "nick"))
            colors.nick = c;
        else if (!strcmp(element, "mynick"))
            colors.my_nick = c;
        else if (!strcmp(element, "mention"))
            colors.nick_mentioned = c;
        else if (!strcmp(element, "action"))
            colors.action = c;
        else if (!strcmp(element, "activity"))
            colors.activity = c;
        else if (!strcmp(element, "important"))
            colors.important_activity = c;
        else
            goto error;
    } else goto error;
    
    return;

error:
    fatal("Invalid color setting in configuration file: `%s`\n"\
          "See the default configuration for a list of valid options.\n"\
          "Color values must be between 0 and 255 (inclusive).", s);
}

static void load_user(char const *s)
{
    char setting[32];
    char value[128];

    if (sscanf(s, "%31s = %127s", setting, value) != 2)
        goto error;

    if (!strcmp(setting, "nick"))
        user.nick = duplicate(value);
    else if (!strcmp(setting, "username"))
        user.username = duplicate(value);
    else if (!strcmp(setting, "auth"))
        user.auth_string = duplicate(value);
    else
        goto error;

    return;

error:
    fatal("Invalid user setting in configuration file: `%s`\n"\
          "See the default configuration for examples of valid "\
          "user settings.");
}

static void load_channel(char const *s)
{
    if (autojoin_count == 10)
        fatal("There are too many autojoin channels in your configuration file.\n"\
              "The maximum number of channels which can be autojoined is 10");

    autojoin[autojoin_count++] = duplicate(s);
}

static void load_misc(char const *s)
{
    char *error_message;
    char option[64];
    char value[64];

    if (sscanf(s, "%63s = %63s", option, value) != 2)
        goto error;

    if (!strcmp(option, "nicklength"))
        goto nicklength;
    else if (!strcmp(option, "autoswitch"))
        goto autoswitch;
    else
        goto error;

nicklength: {
    char *end;
    long len = strtol(value, &end, 10);
    if (len < 6 || len > 30) {
        error_message = "Invalid value for nicklength (must be between 6 an 30 inclusive)";
        goto error;
    }

    if (*end && *end != '\n')
        goto error;

    nicklength = len;

    return;
}

autoswitch:
    if (!strcmp(value, "on"))
        autoswitch = true;
    else if (!strcmp(value, "off"))
        autoswitch = false;
    else
        goto error;

    return;

error:
    fatal("Invalid or unrecognized miscellaneous setting: `%s`", s);
}

static void load_configuration(FILE *f)
{
    char buffer[1024];

    void (*load)(char const *) = NULL;
    while (fgets(buffer, 1024, f)) {
        char *end = strchr(buffer, ';');
        if (end)
            *end = '\0';
        if (!*buffer || *buffer == '\n')
            continue;

        char section[32];
        if (sscanf(buffer, "[%[^]]]", section) == 1) {
            if (!strcmp(section, "user"))
                load = load_user;
            else if (!strcmp(section, "colors"))
                load = load_color;
            else if (!strcmp(section, "channels"))
                load = load_channel;
            else if (!strcmp(section, "handler"))
                load = load_handler;
            else if (!strcmp(section, "misc"))
                load = load_misc;
            else
                fatal("Invalid section in configuration file: `%s`", section);
        } else {
            load(buffer);
        }
    }
}

static void debug_string(char const *s)
{
        record("\n\nString: `%s`\n\n", s);
        record("Length: %zu\n", strlen(s));

        for (char const *c = s; *c; ++c)
                record("Byte %zu: %hhd\n", c - s, *c);

        record("\n\n");
}

static int render_as_color(TickitRenderBuffer *rb, struct color color, char *fmt, ...)
{
    static TickitPen *pen;

    if (!pen)
        pen = tickit_pen_new_attrs(TICKIT_PEN_BG, color.bg, -1);

    tickit_pen_set_colour_attr(pen, TICKIT_PEN_FG, color.fg);
    tickit_pen_set_colour_attr(pen, TICKIT_PEN_BG, color.bg);
    tickit_renderbuffer_setpen(rb, pen);

    va_list ap;
    va_start(ap, fmt);
    int ret = tickit_renderbuffer_vtextf(rb, fmt, ap);
    va_end(ap);

    return ret;
}

static void clear_with_color(TickitRenderBuffer *rb, struct color color)
{
    static TickitPen *pen;

    if (!pen)
        pen = tickit_pen_new_attrs(TICKIT_PEN_BG, -1, -1);

    tickit_pen_set_colour_attr(pen, TICKIT_PEN_FG, color.fg);
    tickit_pen_set_colour_attr(pen, TICKIT_PEN_BG, color.bg);

    tickit_renderbuffer_setpen(rb, pen);

    tickit_renderbuffer_clear(rb);
}

static struct room *get_room(char const *target)
{
    if (!target)
        return &rooms[0];

    for (size_t i = 1; i < room_count; ++i)
        if (!strcmp(rooms[i].target, target))
            return rooms + i;

    return NULL;
}

static struct message *new_message(void)
{
    static time_t timestamp;

    time(&timestamp);

    if (message_count == message_alloc) {
        message_alloc = message_alloc ? message_alloc * 2 : 1;
        messages = realloc(messages, message_alloc * sizeof *messages);
        if (!messages)
            fatal("Out of memory...");
    }

    struct message *result = messages + message_count;
    result->timestamp = timestamp;

    message_count += 1;
    
    atomic_store(&should_render_messages, true);

    return result;
}

static struct nick_node *new_nick_node(char *nick)
{
    struct nick_node *node = malloc(sizeof *node);
    if (!node)
        fatal("Out of memory...");

    node->nick = nick;
    node->next = NULL;

    return node;
}

static size_t column_count(char const *s)
{
    static TickitStringPos limit = { -1, -1, -1, -1 };
    static TickitStringPos result;

    tickit_string_count(s, &result, &limit);

    return result.columns;
}

static size_t fit_in_columns(char const *s, size_t n, bool split_at_space)
{
    static TickitStringPos result;
        TickitStringPos limit = { -1, -1, -1, (int) n };

        tickit_string_count(s, &result, &limit);

        size_t idx = result.bytes;

        if (!split_at_space)
            return idx;

        while (idx && s[idx] && !isspace(s[idx]))
            idx -= 1;

        while (idx > 0 && s[idx] && isspace(s[idx - 1]))
            idx -= 1;

        if (idx)
            return idx;
        else
            return result.bytes;
}

static void room_add_user(struct room *room, char *nick)
{
    if (room->nicks.count == 0) {
        room->nicks.count = 1;
        room->nicks.head = new_nick_node(nick);
    } else {
        room->nicks.count += 1;
        struct nick_node *node = room->nicks.head;

        while (node->next)
            node = node->next;

        node->next = new_nick_node(nick);
    }
}

static bool room_remove_user(struct room *room, char *nick)
{
        struct nick_node *node = room->nicks.head;
        if (!room)
            return false;

        if (!node)
            return false;

        while (node->next && strcmp(node->next->nick, nick))
            node = node->next;
        
        if (!node->next)
            return false;

        room->nicks.count -= 1;
        node->next = node->next->next;

        return true;
}

static struct nick_node *room_get_user(struct room *room, char *nick)
{
        struct nick_node *node = room->nicks.head;
        assert(room);

        while (node && strcmp(node->nick, nick))
            node = node->next;

        return node;
}

static void notify(char *target, char const *fmt, ...)
{
    char notification[1024];

    va_list ap;
    va_start(ap, fmt);
    vsnprintf(notification, 1024, fmt, ap);
    va_end(ap);

    struct message *msg = new_message();

    msg->type = MSG_NOTIFICATION;
    msg->text = duplicate(notification);
    msg->target = target;
    
    atomic_store(&should_render_messages, true);
}

static void warn(char const *fmt, ...)
{
    char warning[4096];

    va_list ap;
    va_start(ap, fmt);
    vsnprintf(warning, sizeof warning, fmt, ap);
    va_end(ap);

    struct message *msg = new_message();

    msg->text = duplicate(warning);
    msg->type = MSG_WARNING;

    if (room)
        msg->target = room->target;
    else
        msg->target = NULL;
}

static bool should_display(struct message const *message)
{
    if (!room->target || !message->target)
        return !room->target && !message->target;

    return !strcmp(message->target, room->target);
}

static void unknown_command(char const *command)
{
    warn("Unknown command: `%s`", command);
}

static void ambiguous_command(char const *command)
{
    return;
}

/*
 * Allocates a new room object and puts in
 * in the list of current rooms. If `go`
 * is true, then make the newly joined room
 * the active room.
 *
 * `target` is a channel name if the room is
 * a channel, or a nick if the room is a private
 * chat with somebody.
 */
static void join_room(char *target, bool go)
{
    atomic_store(&should_render_status, true);
    atomic_store(&should_render_messages, true);

     /*
     * We may need to save the room index so that we can correct
     * the value of `room`, which may become invalidated if `rooms`
     * is re-allocated.
     */
    size_t room_idx;
    if (!go)
        room_idx = room - rooms;

    if (room_count == room_alloc) {
        room_alloc = room_alloc ? room_alloc * 2 : 1;
        rooms = realloc(rooms, room_alloc * sizeof *rooms);
        if (!rooms)
            fatal("Out of memmory...");
    }

    struct room *new_room = rooms + room_count;

    room_count += 1;

    new_room->target = target;
    new_room->topic = NULL;
    new_room->nicks = empty_nick_list;

    if (!target)
        new_room->type = ROOM_SERVER;
    else if (*target == '#')
        new_room->type = ROOM_CHANNEL;
    else
        new_room->type = ROOM_PRIVATE;

    if (go)
        room = new_room;
    else
        room = &rooms[room_idx];
}

/**
 * The main message-drawing function. This is called whenever the
 * message window needs to be re-drawn.
 */
static int expose_messages(TickitWindow *w, TickitEventType e, void *_info, void *data)
{
    static bool called;
    static size_t offset = 0;
    static char timestamp_buffer[16];

    /*
     * If this is first time expose_messages is called,
     * we initialize offset. We also add 2 to nicklength
     * simply to avoid having four occurrences of the
     * expression 'nicklength + 2' below.
     */
    if (!offset) {
        offset = nicklength + 16;
        nicklength += 2;
    }

    if (!atomic_exchange(&should_render_messages, false) && called++)
        return 1;

    TickitExposeEventInfo *info = _info;
    TickitRenderBuffer *buffer = info->rb;
    TickitRect rect = info->rect;

    /* Prevent old messages reminaing on the screen if
     * they aren't covered by new messagees.
     */
    clear_with_color(buffer, colors.normal);

    /* Clear the new activity flag on the current room, since it's
     * no longer new (we're looking at it right now).
     */
    atomic_store(&room->activity, ACTIVITY_NONE);

    
    /* Go backwards rendering the as many messages as can fit on the screen */
    size_t row = 0;
    size_t scroll = scroll_idx;
    for (size_t idx = scroll_idx; idx < message_count && row < rect.lines; ++idx) {
        struct message msg = messages[message_count - idx - 1];

        struct color color = colors.normal;
        if (msg.type == MSG_WARNING)
            color = colors.warning;
        else if (msg.type == MSG_NOTIFICATION)
            color = colors.notification;

        if (!should_display(&msg) || (scroll && --scroll))
            continue;

        struct tm *time_info = localtime(&msg.timestamp);
        strftime(timestamp_buffer, sizeof timestamp_buffer, "%H:%M:%S", time_info);

        size_t span = 0;
        char *text = msg.text;
        while (*text) {
            text += fit_in_columns(text, rect.cols - offset, true);
            span += 1;
        }

        char from_buffer[20] = {0};
        if (msg.type == MSG_NORMAL)
            snprintf(from_buffer, 20, "<%s>", msg.from);
        else if (msg.type == MSG_WARNING)
            strcpy(from_buffer, "!!!    ");
        tickit_renderbuffer_goto(buffer, rect.lines - (row + span), 0);
        render_as_color(buffer, colors.timestamp, " [%s]  ", timestamp_buffer);
        if (msg.type == MSG_NORMAL && !strcmp(msg.from, user.nick))
            render_as_color(buffer, colors.my_nick, "%*.*s ", nicklength, nicklength, from_buffer);
        else
            render_as_color(buffer, colors.nick, "%*.*s ", nicklength, nicklength, from_buffer);

        size_t lines_used = 0;
        while (*msg.text) {
            size_t line_number = rect.lines + lines_used - (row + span);
            tickit_renderbuffer_goto(buffer, line_number, offset);

            size_t n = fit_in_columns(msg.text, rect.cols - offset, true);

            /* The nickname portion of an ACTION message is
             * a special case, since it goes in the message
             * part of the window rather than where nicks
             * usually go.
             */
            if (msg.type == MSG_ACTION && lines_used == 0) {
                render_as_color(buffer, colors.action, "%s ", msg.from);
                n = fit_in_columns(msg.text, rect.cols - offset - column_count(msg.from) - 1, true);
            }

            /* The message was split onto the next line here,
             * so we can skip the next space (the newline suffices
             * to separate the words)
             */
            if (lines_used > 0 && *msg.text == ' ') {
                msg.text += 1;
                n -= 1;
            }

            char save = msg.text[n];
            msg.text[n] = '\0';
            char *our_nick = strstr(msg.text, user.nick);
            bool occurrence =  our_nick
                            && (our_nick == msg.text || !isalnum(*(our_nick - 1)))
                            && !isalnum(*(our_nick + strlen(user.nick)));
            if (occurrence) {
                *our_nick = '\0';
                render_as_color(buffer, color, "%s", msg.text);
                render_as_color(buffer, colors.nick_mentioned, "%s", user.nick);
                render_as_color(buffer, color, "%s", our_nick + strlen(user.nick));
                *our_nick = *user.nick;
            } else {
                render_as_color(buffer, color, "%s", msg.text);
            }

            msg.text[n] = save;

            msg.text += n;

            lines_used += 1;
        }
        row += lines_used;
    }

    tickit_renderbuffer_setpen(buffer, default_pen);

    return 1;
}

static int expose_input_line(TickitWindow *w, TickitEventType e, void *_info, void *data)
{
    static int line;
    static int col;
    static TickitPen *input_pen;

    if (!input_pen)
        input_pen = tickit_pen_new_attrs(TICKIT_PEN_FG, colors.input.fg, TICKIT_PEN_BG, colors.input.bg, -1);

    if (!atomic_exchange(&should_render_input_line, false))
        return 1;


    TickitExposeEventInfo *info = _info;
    TickitRenderBuffer *buffer = info->rb;
    TickitRect rect = info->rect;

    tickit_renderbuffer_setpen(buffer, input_pen);
    tickit_renderbuffer_clear(buffer);
    
    size_t offset = 0;
    char save = input_buffer[cursor_bytes];
    input_buffer[cursor_bytes] = '\0';
    if (column_count(input_buffer) + column_count(user.nick) + 6 >= rect.cols)
        offset = fit_in_columns(input_buffer, column_count(input_buffer) + column_count(user.nick) + 6 - rect.cols + 1, false);
    input_buffer[cursor_bytes] = save;

    tickit_renderbuffer_goto(buffer, 0, 0);
    tickit_renderbuffer_textf(buffer, " [%s]: %s", user.nick, input_buffer + offset);

    tickit_renderbuffer_goto(buffer, 0, 0);
    tickit_renderbuffer_textf(buffer, " [%s]: ", user.nick);
    tickit_renderbuffer_textn(buffer, input_buffer + offset, cursor_bytes - offset);

    tickit_renderbuffer_get_cursorpos(buffer, &line, &col);
    tickit_window_set_cursor_position(w, line, col);


    return 1;
}

static int expose_status(TickitWindow *w, TickitEventType e, void *_info, void *data)
{
    static bool called;

    if (!atomic_exchange(&should_render_status, false) && called++)
        return 1;

    TickitExposeEventInfo *info = _info;
    TickitRenderBuffer *buffer = info->rb;
    TickitRect rect = info->rect;

    clear_with_color(buffer, colors.normal);

    tickit_renderbuffer_goto(buffer, 0, 0);

    struct color color;
    for (size_t i = 0; i < room_count; ++i) {

        unsigned char activity = atomic_load(&rooms[i].activity);

        if (activity == ACTIVITY_IMPORTANT)
            color = colors.important_activity;
        else if (activity == ACTIVITY_NORMAL)
            color = colors.activity;
        else
            color = colors.normal;

        if (&rooms[i] == room)
            color = colors.normal;

        if (rooms + i == room && room->type == ROOM_CHANNEL)
            render_as_color(buffer, color, " [%s:%zu] ", rooms[i].target, rooms[i].nicks.count);
        else if (rooms + i == room && room->type == ROOM_PRIVATE)
            render_as_color(buffer, color, " [%s:private] ", rooms[i].target);
        else if (rooms[i].type == ROOM_SERVER && room->target)
            render_as_color(buffer, color, " server ", rooms[i].target);
        else if (rooms[i].type == ROOM_SERVER && !room->target)
            render_as_color(buffer, color, " [server] ", rooms[i].target);
        else
            render_as_color(buffer, color, " %s ", rooms[i].target);
    }

    return 1;
}

static int scroll_messages(TickitWindow *t, TickitEventType e, void *_info, void *data)
{
    TickitMouseEventInfo *info = _info;

    if (info->type != TICKIT_MOUSEEV_WHEEL)
        return 1;

    if (info->button == TICKIT_MOUSEWHEEL_UP) {
        if (scroll_idx == message_count)
            return 1;
        scroll_idx += 1;
    } else {
        if (scroll_idx == 0)
            return 1;
        scroll_idx -= 1;
    }

    atomic_exchange(&should_render_messages, true);

    return 1;
}

static void irc_message_record(struct irc_reply const *reply)
{
    record("===========================\n");

    char const *type = irc_str_type(reply);

    if (type)
        record("Reply type: %s\n", type);
    else
        record("Reply type: UNRECOGNIZED\n");
        

    if (reply->has_prefix) {
        if (reply->prefix.type == IRC_PREFIX_SERVER) {
            record("Server name: %s\n", reply->prefix.server);
        } else {
            record("Nick: %s\n", reply->prefix.nick);
            if (reply->prefix.host)
                record("Host: %s\n", reply->prefix.host);
            else
                record("Host: (null)\n");
            if (reply->prefix.user)
                record("User: %s\n", reply->prefix.user);
            else
                record("User: (null)\n");
        }
    }

    record("Number of paramters: %zu\n", reply->paramc);
    record("Parameters:\n");
    for (size_t i = 0; i < reply->paramc; ++i)
        record("\t%zu. %s\n", i + 1, reply->paramv[i]);

    record("===========================\n");
}

static struct irc_reply irc_reply_parse(char *text)
{
    static char first[256], second[256], third[256];
    static char separator[4];
    struct irc_reply reply;

    reply.type = IRC_NOT_IMPLEMENTED;
    reply.has_prefix = false;

    if (*text == ':') {

        text += 1;

        reply.has_prefix = true;

        int matched = sscanf(
                text,
                "%255[^ @!]%1[^ ]%255[^ @]%c%255[^ ]",
                first,
                separator,
                second,
                separator + 2,
                third
        );

        if (matched == 0)
            fatal("Received an IRC message with an invalid format: `%s`", text);

        size_t consumed;

        if (matched == 1) {
            consumed = strlen(first);
            if (strchr(first, '.')) {
                reply.prefix.type = IRC_PREFIX_SERVER;
                reply.prefix.server = duplicate(first);
            } else {
                reply.prefix.type = IRC_PREFIX_USER;
                reply.prefix.nick = duplicate(first);
                reply.prefix.user = NULL;
                reply.prefix.host = NULL;
            }
        } else {
            reply.prefix.type = IRC_PREFIX_USER;
            reply.prefix.nick = duplicate(first);
            if (separator[0] == '!') {
                consumed = strlen(first) + strlen(second) + strlen(third) + 2;
                reply.prefix.user = duplicate(second);
                reply.prefix.host = duplicate(third);
            } else {
                consumed = strlen(first) + strlen(second) + 1;
                reply.prefix.host = duplicate(second);
                reply.prefix.user = NULL;
            }
        }

        text += consumed;

        if (*text != ' ')
            fatal("Error parsing IRC message. Expecting ' ' but found: `%c`", *text);
    }
    
    /* We re-use the `first` buffer to parse the command */
    int chars;
    int matched = sscanf(text, "%255s%n", first, &chars);

    if (!matched)
        fatal("No command in IRC message: `%s`", text);

    text += chars;

    for (size_t i = 0; i < irc_replies; ++i) {
        if (!strcmp(irc_reply_table[i].string, first)) {
            reply.type = irc_reply_table[i].type;
            break;
        }
    }

    /* Parse up to 15 parameters */
    size_t idx;
    size_t alloc = 0;
    reply.paramc = 0;
    reply.paramv = NULL;
    bool last_parameter = false;
    for (;;) {
        while (*text == ' ')
            text += 1;

        if (reply.paramc == alloc) {
            alloc = alloc ? alloc * 2 : 1;
            reply.paramv = realloc(reply.paramv, alloc * sizeof *reply.paramv);
            if (!reply.paramv)
                fatal("Out of memory...");
        }

        if (*text == ':') {
            text += 1;
            reply.paramv[reply.paramc++] = duplicate(text);
            break;
        }

        idx = 0;
        while (text[idx] && text[idx] != ' ')
            idx += 1;

        if (text[idx])
            text[idx] = '\0';
        else
            last_parameter = true;

        reply.paramv[reply.paramc++] = duplicate(text);

        if (last_parameter)
            break;
        else
            text += idx + 1;
    }

    return reply;
}

static char *irc_receive(void)
{
    char *message = NULL;
    size_t alloc = 0, length = 0;
    char c;

    ssize_t n;
    while (n = read(connection, &c, 1), n == 1) {
        if (length == alloc) {
            alloc = alloc * 2 + 4;
            message = realloc(message, alloc);
            if (!message) fatal("Out of memory...");
        }

        message[length++] = c;

        bool finished = length > 2 &&
                        message[length - 2] == '\r' &&
                        message[length - 1] == '\n';

        if (finished)
            goto end;
    }

    if (n == -1)
        fatal("Lost connection to the server");

    if (length == 0)
        return NULL;

end:
    message[length - 2] = '\0';

    record("RECEIVED: %s\n", message);

    return message;
}

static void irc_send(char *fmt, ...)
{
    static size_t bytes;
    static char buffer[513];
    va_list ap;
    va_start(ap, fmt);
    bytes = vsnprintf(buffer, 513, fmt, ap) + 2;
    va_end(ap);

    record("SENDING: %s\n", buffer);

    buffer[bytes] = '\0';
    buffer[bytes - 1] = '\n';
    buffer[bytes - 2] = '\r';
    write(connection, buffer, bytes);
}

static bool irc_wait_for(char const *success, char const *failure)
{
    char *message;

    while (message = irc_receive()) {
        if (strstr(message, success))
            return true;
        else if (failure && strstr(message, failure))
            return false;
        free(message);
    }

    return false;
}

static void input_insert(char *s)
{
    memmove(input_keys + input_idx + 1, input_keys + input_idx, (input_count - input_idx) * sizeof *input_keys);
    input_keys[input_idx] = s;
    input_idx += 1;
    input_count += 1;
}

static void command_join(char *parameter)
{
    static char channel[128];

    if (sscanf(parameter, "%128s", channel) != 1) {
        warn("Invalid argument to /join: %s", parameter);
        return;
    }

    irc_send("JOIN %s", channel);
}

static void command_raw(char *parameter)
{
    irc_send("%s", parameter);
}

static void command_msg(char *parameter)
{
    static char target_buffer[256];
    static int idx;

    if (sscanf(parameter, "%255s%n", target_buffer, &idx) != 1) {
        warn("Invalid argument to /msg: %s", parameter);
        return;
    }

    if (parameter[idx] == ' ')
        idx += 1;

    char *target = duplicate(target_buffer);

    irc_send("PRIVMSG %s :%s", target, parameter + idx);

    struct room *room = get_room(target);

    if (!room) {
        if (*target == '#')
            command_join(target);
        else
            join_room(target, true);
    }

    irc_privmsg(user.nick, target, parameter + idx);
}

static void command_action(char *parameter)
{
    static char action_buffer[2048];

    if (!room->target)
        return;

    snprintf(action_buffer, sizeof action_buffer, "%cACTION %s%c", 0x01, parameter, 0x01);

    irc_send("PRIVMSG %s :%s", room->target, action_buffer);
    irc_privmsg(user.nick, room->target, duplicate(action_buffer));
}

static void command_part(char *parameter)
{
    if (!room->target)
        return;

    atomic_store(&should_render_status, true);
    atomic_store(&should_render_messages, true);

    if (room->type == ROOM_CHANNEL)
        irc_send("PART %s :%s", room->target, parameter);

    size_t room_idx = room - rooms;

    if (room_idx + 1 == room_count)
        room -= 1;
    else
        memmove(room, room + 1, (room_count - room_idx) * sizeof *room);

    room_count -= 1;

    if (room_count == 0)
        exit(EXIT_SUCCESS);
}

static void command_quit(char *parameter)
{
    if (!parameter || !*parameter)
        irc_send("QUIT");
    else
        irc_send("QUIT :%s", parameter);

    exit(EXIT_SUCCESS);
}

static void command_here(char *parameter)
{
    if (!room->target)
        return;

    bool here = room_get_user(room, parameter);

    if (here)
        notify(room->target, "%s is here", parameter);
    else
        notify(room->target, "%s is not here", parameter);
}

static void command_topic(char *parameter)
{
    if (!room->target) {
        warn("The server does not have a topic");
        return;
    } else if (!room->topic) {
        warn("%s does not have a topic", room->target);
    }

    notify(room->target, "Topic for %s: %s", room->target, room->topic);
}

static bool irc_authenticate
(
    char const *nick,
    char const *user,
    char const *host,
    char const *realname,
    char const *auth_string
)
{
    if (!flag_no_sasl)
        irc_send("CAP REQ :sasl");

    irc_send("NICK %s", nick);
    irc_send("USER %s %s _ :%s", user, host, realname);

    if (flag_no_sasl)
        return true;

    if (!irc_wait_for("ACK :sasl", NULL))
        return false;

    irc_send("AUTHENTICATE PLAIN");

    if (!irc_wait_for("AUTHENTICATE +", NULL))
        return false;

    irc_send("AUTHENTICATE %s", auth_string);

    if (!irc_wait_for("successful", "failed"))
        return false;

    irc_send("CAP END");

    return true;
}

static bool irc_connect(char const *host, char const *port)
{
    struct addrinfo hints, *result;

    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(host, port, &hints, &result) != 0)
        return false;
    if ((connection = socket(result->ai_family, result->ai_socktype, result->ai_protocol)) == -1)
        return false;
    if (connect(connection, result->ai_addr, result->ai_addrlen) == -1)
        return false;

    return true;
}

static void handle_user_join(char *joined_nick, char *joined_user, char *joined_host, char *channel)
{
    atomic_store(&should_render_status, true);

    struct room *room = get_room(channel);
    if (!room)
        return;

    room_add_user(room, joined_nick);

    notify(channel, "%s has joined %s (%s!%s@%s)", joined_nick, channel, joined_nick, joined_user, joined_host);
}

static void handle_user_part(char *parting_nick, char *channel, char *message)
{
    atomic_store(&should_render_status, true);

    struct room *room = get_room(channel);
    if (!room)
        return;

    room_remove_user(room, parting_nick);

    if (message)
        notify(channel, "%s has left %s (%s)", parting_nick, channel, message);
    else
        notify(channel, "%s has left %s", parting_nick, channel);
}

static void handle_user_quit(char *quitting_nick, char *message)
{
    atomic_store(&should_render_status, true);

    for (size_t i = 0; i < room_count; ++i) {
        if (!room_remove_user(rooms + i, quitting_nick))
            continue;
        if (message)
            notify(rooms[i].target, "%s has quit (%s)", quitting_nick, message);
        else
            notify(rooms[i].target, "%s has quit", quitting_nick);
    }
}

static void room_add_nicks(char const *channel, char *nicks)
{
    atomic_store(&should_render_status, true);

    struct room *room = get_room(channel);
    if (!room)
        return;

    struct nick_node *node = room->nicks.head;

    while (node->next)
        node = node->next;

    for (char *n = strtok(nicks, " "); n; n = strtok(NULL, " ")) {
        if (!strcmp(user.nick, n))
            continue;
        node->next = new_nick_node(n);
        node = node->next;
        room->nicks.count += 1;
    }
}

static void room_set_topic(char const *channel, char *topic)
{
    atomic_store(&should_render_status, true);

    struct room *room = get_room(channel);
    if (!room)
        return;

    room->topic = topic;
}

static void irc_privmsg(char *from, char *target, char *text)
{
    atomic_store(&should_render_messages, true);

    struct message *message = new_message();

    if (*text == 0x01) {
        message->type = MSG_ACTION;
        text += 8;
        text[strlen(text) - 1] = '\0';
    } else {
        message->type = MSG_NORMAL;
    }

    message->target = target;
    message->from = from;
    
    if (is_utf8(text))
        message->text = text;
    else {
        message->text = duplicate("<invalid utf-8 text>");
        record("\n\n|%s|\n\n", text);
        debug_string(text);
    }
    
    if (room->target && target && strcmp(room->target, target)) {
        struct room *r = get_room(target);
        if (!r)
            fatal("FAILED GET_ROOM FOR: `%s`", target);

        if (r == room);
        else if (contains_nick(text))
            atomic_store(&r->activity, ACTIVITY_IMPORTANT);
        else
            atomic_store(&r->activity, ACTIVITY_NORMAL);

        atomic_store(&should_render_status, true);
    }

}

static void tab_completion(void)
{
#define last(s) ((s)[strlen((s)) - 1])

    if (input_idx == 0)
        return;

    if (!room)
        return;

    size_t idx = input_idx - 1;
    while (idx && last(input_keys[idx]) != ' ')
        idx -= 1;

    bool add_colon = !idx;

    size_t start;
    if (last(input_keys[idx]) != ' ')
        start = idx;
    else
        start = idx + 1;

    char prefix[512] = {0};
    for (size_t i = start; i < input_idx; ++i)
        strcat(prefix, input_keys[i]);

    size_t length = strlen(prefix);

    char *suggestion = NULL;
    size_t checked = 0;
    for (size_t i = 1; i <= message_count && checked < 50; ++i) {
        struct message msg = messages[message_count - i];

        if (msg.type != MSG_NORMAL)
            continue;

        if (strcmp(msg.target, room->target))
            continue;

        checked += 1;

        if (strncmp(msg.from, prefix, length))
            continue;

        suggestion = malloc(strlen(msg.from) - length + 3);
        if (!suggestion)
            fatal("Out of memory...");

        strcpy(suggestion, msg.from + length);

        break;
    }

    if (!suggestion)
        return;

    input_insert(suggestion);

    if (add_colon)
        input_insert(": ");

#undef last
}

void handle_outbound_message(char *message)
{
    if (*message == '/') {
        message += 1;
        char *c = strchr(message, ' ');
        if (c)  {
            *c = '\0';
            run_command(message, c + 1);
        } else {
            run_command(message, "");
        }
    } else if (room->target) {
        irc_send("PRIVMSG %s :%s", room->target, message);
        irc_privmsg(user.nick, room->target, message);
    } else {
        /* We're not in a room. Send this directly to the server. */
        irc_send("%s", message);
    }
}

void handle_inbound_message(char *message)
{
    struct irc_reply msg = irc_reply_parse(message);
    free(message);

    atomic_store(&should_render_messages, true);

    /* Write the message to the log file */
    irc_message_record(&msg);

    /* If the user has defined an external message handler, use it here */
    if (ext_handler_fd != -1)
        irc_write_json(&msg, ext_handler_fd);

    switch (msg.type) {
    case IRC_PING:
        atomic_store(&should_pong, true);
        break;
    case IRC_PRIVMSG:
        if (!strcmp(msg.paramv[0], user.nick)) {
            if (!get_room(msg.prefix.nick))
                join_room(msg.prefix.nick, autoswitch);
            irc_privmsg(msg.prefix.nick, msg.prefix.nick, msg.paramv[1]);
        } else {
            irc_privmsg(msg.prefix.nick, msg.paramv[0], msg.paramv[1]);
        }
        break;
    case IRC_JOIN:
        if (!strcmp(msg.prefix.nick, user.nick))
            join_room(msg.paramv[0], true);
        handle_user_join(msg.prefix.nick, msg.prefix.user, msg.prefix.host, msg.paramv[0]);
        break;
    case IRC_PART:
        if (strcmp(msg.prefix.nick, user.nick)) {
            char *message = msg.paramc == 2 ? msg.paramv[1] : NULL;
            handle_user_part(msg.prefix.nick, msg.paramv[0], message);
        }
        break;
    case IRC_QUIT:
        if (strcmp(msg.prefix.nick, user.nick)) {
            char *message = msg.paramc == 1 ? msg.paramv[0] : NULL;
            handle_user_quit(msg.prefix.nick, message);
        }
        break;
    case IRC_NAMES:
        room_add_nicks(msg.paramv[2], msg.paramv[3]);
        break;
    case IRC_TOPIC:
        room_set_topic(msg.paramv[1], msg.paramv[2]);
        break;
    case IRC_MODE:
        if (msg.paramc == 3) /* Channel mode */
            notify(msg.paramv[0], "%s sets mode %s for %s", msg.prefix.nick, msg.paramv[1], msg.paramv[2]);
        else                 /* User mode */
            notify(NULL, "%s sets mode %s for %s", msg.prefix.nick, msg.paramv[1], msg.paramv[0]);
        break;
    case IRC_NOTICE:
        notify(NULL, "(%s) %s", msg.prefix.nick, msg.paramv[1]);
        break;
    default:
        break;
    }
}

static int handle_input(TickitTerm *t, TickitEventType e, void *_info, void *data)
{
    TickitKeyEventInfo *info = _info;

    atomic_store(&should_render_input_line, true);

    if (info->type == TICKIT_KEYEV_KEY) {
        if (!strcmp(info->str, "Enter")) {
            handle_outbound_message(duplicate(input_buffer));
            input_idx = 0;
            input_count = 0;
        } else if (!strcmp(info->str, "C-c")) {
            exit(EXIT_SUCCESS);
        } else if (input_idx > 0 && !strcmp(info->str, "Backspace")) {
            memmove(input_keys + input_idx - 1, input_keys + input_idx, (input_count - input_idx) * sizeof *input_keys);
            input_idx -= 1;
            input_count -= 1;
        } else if (room != rooms && !strcmp(info->str, "M-Left")) {
            atomic_store(&should_render_messages, true);
            atomic_store(&should_render_status, true);
            pthread_mutex_lock(&lock);
            room -= 1;
            pthread_mutex_unlock(&lock);
        } else if (room != &rooms[room_count - 1] && !strcmp(info->str, "M-Right")) {
            atomic_store(&should_render_status, true);
            atomic_store(&should_render_messages, true);
            pthread_mutex_lock(&lock);
            room += 1;
            pthread_mutex_unlock(&lock);
        } else if (room && !strcmp(info->str, "C-w")) {
            command_part("Leaving...");
        } else if (input_idx > 0 && !strcmp(info->str, "Left")) {
            input_idx -= 1;
        } else if (input_idx < input_count && !strcmp(info->str, "Right")) {
            input_idx += 1;
        } else if (!strcmp(info->str, "C-a")) {
            input_idx = 0;
        } else if (!strcmp(info->str, "C-e")) {
            input_idx = input_count;
        } else if (!strcmp(info->str, "C-k")) {
            /*
             * Ctrl + K is dual-purposed. If there is no text
             * after the cursor, it scrolls up.
             *
             * Otherwise it's like readline Ctrl + K: it deletes
             * any text adter the cursor.
             */
            if (input_idx == input_count) {
                scroll_idx += 5;
                atomic_store(&should_render_messages, true);
            } else
                input_count = input_idx;
        } else if (!strcmp(info->str, "C-j")) {
                atomic_store(&should_render_messages, true);
                if (scroll_idx < 5)
                    scroll_idx = 0;
                else
                    scroll_idx -= 5;
        } else if (!strcmp(info->str, "Tab")) {
            tab_completion();
        }
    } else {
        input_insert(duplicate(info->str));
    }

    /* Re-construct the contents of the input buffer */
    input_buffer[0] = '\0';
    cursor_bytes = 0;
    for (size_t i = 0; i < input_count; ++i) {
        strcat(input_buffer, input_keys[i]);
        if (i < input_idx)
            cursor_bytes += strlen(input_keys[i]);
    }

    return 0;
}

static int handle_resize(TickitTerm *t, TickitEventType e, void *_info, void *data)
{
    TickitResizeEventInfo *info = _info;

    atomic_store(&should_render_messages, true);
    atomic_store(&should_render_input_line, true);
    atomic_store(&should_render_status, true);

    rows = info->lines;
    columns = info->cols;

    TickitRect msgrect = {0, 0, rows - 2, columns};
    TickitRect inputrect = {rows - 2, 0, 1, columns};
    TickitRect statusrect = {rows - 1, 0, 1, columns};

    tickit_window_set_geometry(windows.messages, msgrect);
    tickit_window_set_geometry(windows.input, inputrect);
    tickit_window_set_geometry(windows.status, statusrect);

    return 1;
}

static void *inbound_listener(void *unused)
{
    char *message;
    for (;;) {
        message = irc_receive();

        pthread_mutex_lock(&lock);
        handle_inbound_message(message);
        pthread_mutex_unlock(&lock);

        usleep(10000);
    }

    return NULL;
}

static void run_command(char const *command, char *parameter)
{
    void (*f)(char *) = NULL;

    for (size_t i = 0; i < command_count; ++i) {
        if (strstr(command_table[i].name, command) == command_table[i].name) {
            if (f) {
                ambiguous_command(command);
                return;
            } else {
                f = command_table[i].function;
            }
        }
    }

    if (!f) {
        unknown_command(command);
        return;
    }

    f(parameter);
}

int main(int argc, char *argv[])
{
    atexit(cleanup);

    if (argc > 1) {
        for (argv += 1; *argv; ++argv) {
            if (!strcmp(*argv, "--no-sasl"))
                flag_no_sasl = true;
            else if (!strcmp(*argv, "--no-handler"))
                flag_no_handler = true;
            else if (!strncmp(*argv, "--network=", 10))
                flag_network = *argv + 10;
        }
    }

    log_file = fopen("LOG", "w");
    if (!log_file)
        fatal("Failed to open log file");

    port = "6667";

    char *home = getenv("HOME");
    if (!home)
        fatal("Couldn't get HOME from the environment");

    char config_name[512];
    snprintf(config_name, sizeof config_name, "%s/.irc.conf", home);

    FILE *config = fopen(config_name, "r");
    if (!config)
        fatal("Failed to open configuration file. Please generate the default "\
              "configuration file at ~/.irc.conf by running the setup script.");

    load_configuration(config);
    fclose(config);

    if (!irc_connect(flag_network, port))
        fatal("Couldn't connect to %s:%s", flag_network, port);

    if (!irc_authenticate(user.nick, user.username, flag_network, user.real_name, user.auth_string))
        fatal("Failed to authenticate as user %s", user.username);

    /* Join a room that will serve as your "connection to the server" */
    join_room(NULL, true);

    /* Start handling messages from the server */
    record("STARTING LISTENER THREAD\n");
    if (pthread_create(&listener_thread, NULL, inbound_listener, NULL) != 0)
        fatal("Failed to spawn inbound listener thread");

    default_pen = tickit_pen_new_attrs(TICKIT_PEN_BG, -1, -1);

    t = tickit_term_open_stdio();
    if (!t)
        fatal("Couldn't create TickitTerm: %s", strerror(errno));

    tickit_term_await_started_msec(t, 100);

    tickit_term_get_size(t, &rows, &columns);

    tickit_term_setctl_int(t, TICKIT_TERMCTL_CURSORVIS, 1);
    tickit_term_setctl_int(t, TICKIT_TERMCTL_ALTSCREEN, 1);
    tickit_term_setctl_int(t, TICKIT_TERMCTL_MOUSE, TICKIT_TERM_MOUSEMODE_MOVE);

    tickit_term_bind_event(t, TICKIT_EV_KEY, handle_input, NULL);
    tickit_term_bind_event(t, TICKIT_EV_RESIZE, handle_resize, NULL);

    windows.root = tickit_window_new_root(t);

    TickitRect msgrect = {0, 0, rows - 2, columns};
    TickitRect inputrect = {rows - 2, 0, 1, columns};
    TickitRect statusrect = {rows - 1, 0, 1, columns};


    windows.messages = tickit_window_new(windows.root, msgrect, 0);
    windows.input = tickit_window_new(windows.root, inputrect, 0);
    windows.status = tickit_window_new(windows.root, statusrect, 0);

    assert(windows.root);
    assert(windows.messages);
    assert(windows.input);

    tickit_window_bind_event(windows.messages, TICKIT_EV_EXPOSE, expose_messages, NULL);
    tickit_window_bind_event(windows.input, TICKIT_EV_EXPOSE, expose_input_line, NULL);
    tickit_window_bind_event(windows.status, TICKIT_EV_EXPOSE, expose_status, NULL);

    tickit_window_bind_event(windows.messages, TICKIT_EV_MOUSE, scroll_messages, NULL);

    /* Autojoin specified channels on startup */
    for (size_t i = 0; i < autojoin_count; ++i) {
        irc_send("JOIN %s", autojoin[i]);
        usleep(200000);
    }

    /* C-c is handled manually to do cleanup */
    signal(SIGINT, sigint);

    for (;;) {
        tickit_term_input_wait_msec(t, 100);
        tickit_term_refresh_size(t);
        
        pthread_mutex_lock(&lock);

        tickit_term_setctl_int(t, TICKIT_TERMCTL_CURSORVIS, 0);
        tickit_window_flush(windows.root);
        tickit_window_expose(windows.root, NULL);
        tickit_window_take_focus(windows.input);
        tickit_term_setctl_int(t, TICKIT_TERMCTL_CURSORVIS, 1);

        if (atomic_exchange(&should_pong, false))
            irc_send("PONG");

        pthread_mutex_unlock(&lock);
    }

    return 0;
}
