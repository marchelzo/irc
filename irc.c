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

#include <unistd.h>
#include <netdb.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <pthread.h>

#include <tickit.h>

/* Forward declarations of command handlers */
static void command_join(char *);
static void command_raw(char *);

enum irc_reply_type {
    IRC_ERROR,
    IRC_JOIN,
    IRC_MODE,
    IRC_MOTD,
    IRC_MOTD_END,
    IRC_MOTD_START,
    IRC_NAMES_REPLY,
    IRC_NAMES_END,
    IRC_NEED_MORE_PARAMS,
    IRC_NOTICE,
    IRC_NOT_IMPLEMENTED,
    IRC_PART,
    IRC_PING,
    IRC_PRIVMSG,
    IRC_QUIT,
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
    enum { ROOM_PRIVATE, ROOM_CHANNEL } type;
    char *target;
    struct nick_list nicks;
};

struct message {
    time_t timestamp;
    char *channel;
    char *text;
};

typedef void (*command_function)(char *);

struct { char const *name; command_function function; } command_table[] = {
    { "join", command_join },
    { "raw",  command_raw }
};

static size_t const command_count = sizeof command_table / sizeof command_table[0];

struct { char const *string; enum irc_reply_type type; } irc_reply_table[] = {
    { "372",     IRC_MOTD },
    { "ERROR",   IRC_ERROR },
    { "NOTICE",  IRC_NOTICE },
    { "PART",    IRC_PART },
    { "PRIVMSG", IRC_PRIVMSG },
    { "375",     IRC_MOTD_START },
    { "376",     IRC_MOTD_END },
    { "PING",    IRC_PING },
    { "461",     IRC_NEED_MORE_PARAMS },
    { "421",     IRC_UNKNOWN_COMMAND },
    { "353",     IRC_NAMES_REPLY },
    { "366",     IRC_NAMES_END },
    { "001",     IRC_WELCOME },
    { "MODE",    IRC_MODE },
    { "QUIT",    IRC_QUIT },
    { "JOIN",    IRC_JOIN }
};

static size_t const irc_replies = sizeof irc_reply_table / sizeof irc_reply_table[0];

static int connection;

static char *nick;
static char *host;
static char *port;
static char *auth_string;

static size_t input_length;
static char input_buffer[1024];

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

static int rows;
static int columns;

static struct message *messages;
static size_t message_count;
static size_t message_alloc;

static struct room *room;
static struct room *rooms;
static size_t room_count;
static size_t room_alloc;

static atomic_bool should_render;
static atomic_bool should_pong;

static FILE *log_file;

static void record(char const *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vfprintf(log_file, fmt, ap);
    va_end(ap);
    fflush(log_file);
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

static void notify(char const *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    va_end(ap);

    return;
}

static char *duplicate(char const *s)
{
    size_t length = strlen(s);
    char *result = malloc(length + 1);

    if (!result) fatal("Out of memory...");

    strcpy(result, s);

    return result;
}

static size_t column_count(char const *s)
{
    static TickitStringPos limit = { -1, -1, -1, -1 };
    static TickitStringPos result;

    tickit_string_count(s, &result, &limit);

    return result.columns;
}

static size_t fit_in_columns(char const *s, size_t n)
{
    static TickitStringPos result;
        TickitStringPos limit = { -1, -1, -1, (int) n };

        tickit_string_count(s, &result, &limit);

        size_t idx = result.bytes;

        while (idx && s[idx] && !isspace(s[idx]))
            idx -= 1;

        return idx;
}

static void unknown_command(char const *command)
{
    return;
}

static void ambiguous_command(char const *command)
{
    return;
}

static void irc_message_record(struct irc_reply const *reply)
{
    record("===========================\n");

    bool implemented = false;
    for (size_t i = 0; i < irc_replies; ++i) {
        if (reply->type == irc_reply_table[i].type) {
            implemented = true;
            record("Reply type: %s\n", irc_reply_table[i].string);
            break;
        }
    }

    if (!implemented)
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

    while (read(connection, &c, 1) == 1) {
        if (length == alloc) {
            alloc = alloc * 2 + 2;
            message = realloc(message, alloc);
            if (!message) fatal("Out of memory...");
        }

        message[length++] = c;

        bool finished = true;
        finished &= length > 2;
        finished &= message[length - 2] == '\r';
        finished &= message[length - 1] == '\n';

        if (finished)
            goto end;
    }

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

static void command_join(char *parameter)
{
    static char channel[128];

    if (sscanf(parameter, "%128s", channel) != 1) {
        warn("Invalid argument to /join: %s", parameter);
        return;
    }

}

static void command_raw(char *parameter)
{
    irc_send("%s", parameter);
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
    irc_send("CAP REQ :sasl");
    irc_send("NICK %s", nick);
    irc_send("USER %s %s _ :%s", user, host, realname);

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

/* Helper functions for handling various 
 * events that occur throughout an IRC
 * session. e.g.: incoming PRIVMSG or NOTICE,
 * JOIN / PART notifications, etc.
 */
static void irc_privmsg(char *nick, char *channel, char *text)
{
    static time_t timestamp;

    time(&timestamp);
    
    if (message_count == message_alloc) {
        message_alloc = message_alloc ? message_alloc * 2 : 1;
        messages = realloc(messages, message_alloc * sizeof *messages);
        if (!messages)
            fatal("Out of memory...");
    }

    char buffer[1024];

    snprintf(buffer, 1024, "<%s>: %s", nick, text);

    messages[message_count].channel = channel;
    messages[message_count].text = duplicate(buffer);
    messages[message_count].timestamp = timestamp;

    message_count += 1;
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
            run_command(message, NULL);
        }
    } else {
        irc_send("PRIVMSG %s :%s", room->target, message);
        irc_privmsg(nick, room->target, message);
    }
}

void handle_inbound_message(char *message)
{
    struct irc_reply msg = irc_reply_parse(message);
    free(message);

    atomic_store(&should_render, true);

#ifdef DEBUG
    irc_message_record(&msg);
#endif

    switch (msg.type) {
    case IRC_PING:
        atomic_store(&should_pong, true);
        break;
    case IRC_PRIVMSG:
        irc_privmsg(msg.prefix.nick, msg.paramv[0], msg.paramv[1]);
        break;
    }
}

static int handle_input(TickitTerm *t, TickitEventType e, void *_info, void *data)
{
    TickitKeyEventInfo *info = _info;

    record("INPUT EVENT: %s\n", info->str);

    atomic_store(&should_render, true);

    if (info->type == TICKIT_KEYEV_KEY) {
        if (!strcmp(info->str, "Enter")) {
            handle_outbound_message(duplicate(input_buffer));
            input_buffer[0] = '\0';
            input_length = 0;
        } else if (!strcmp(info->str, "C-c")) {
            exit(EXIT_SUCCESS);
        } else if (input_length > 0 && !strcmp(info->str, "Backspace")) {
            input_buffer[--input_length] = '\0';
        }
    } else {
        unsigned length = strlen(info->str);
        memcpy(input_buffer + input_length, info->str, length);
        input_length += length;
        input_buffer[input_length] = '\0';
    }

    return 0;
}

static int handle_resize(TickitTerm *t, TickitEventType e, void *_info, void *data)
{
    TickitResizeEventInfo *info = _info;

    rows = info->lines;
    columns = info->cols;

    return 1;
}

void *inbound_listener(void *unused)
{
    char *message;
    for (;;) {
        message = irc_receive();

        pthread_mutex_lock(&lock);

        record("LISTENER: GOT LOCK\n");
        
        pthread_mutex_unlock(&lock);

        handle_inbound_message(message);

        usleep(10000);
    }

    return NULL;
}

void render_screen(TickitTerm *t)
{
    tickit_term_clear(t);

    static size_t const offset = 12;
    static char timestamp_buffer[16];

    /* Go backwards rendering the as many messages as can fit on the screen */
    size_t row = 2;
    size_t idx = 0;
    while (idx < message_count && row < rows) {
        struct message msg = messages[message_count - idx - 1];
        struct tm *time_info = localtime(&msg.timestamp);
        strftime(timestamp_buffer, sizeof timestamp_buffer, "%H:%M:%S", time_info);
        size_t lines = column_count(msg.text) / (columns - offset) + 1;
        tickit_term_goto(t, rows - row - lines - 1, 0);
        tickit_term_printf(t, "[%s]", timestamp_buffer);
        size_t to_write = strlen(msg.text);
        while (to_write > 0) {
            size_t n = fit_in_columns(msg.text, columns - offset);
            tickit_term_goto(t, rows - row - lines - 1, offset);
            tickit_term_printn(t, msg.text, n);
            msg.text += n;
            to_write -= n;
            lines -= 1;
        }
        idx += 1;
        row += lines;
    }

    /* Render input line at the bottom of the terminal */
    tickit_term_goto(t, rows - 1, 0);
    tickit_term_printf(t, "[%s]: %s", nick, input_buffer);

    tickit_term_flush(t);
}

void run_command(char const *command, char *parameter)
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
    /* Open log file for debugging */
    log_file = fopen("LOG", "w");
    if (!log_file)
        fatal("Failed to open log file");

    nick = "marchelzo_";
    host = "irc.freenode.net";
    port = "6667";

    auth_string = getenv("IRC_AUTH_STRING");
    if (!auth_string)
        fatal("Couldn't find IRC_AUTH_STRING environment variable");

    if (!irc_connect(host, port))
        fatal("Couldn't connect to %s:%s", host, port);

    if (!irc_authenticate(nick, nick, host, nick, auth_string))
        fatal("Failed to authenticate as user %s", nick);

    /* Start handling messages from the server */
    pthread_t inbound_thread;
    if (pthread_create(&inbound_thread, NULL, inbound_listener, NULL) != 0)
        fatal("Failed to spawn inbound listener thread");

    TickitTerm *t = tickit_term_open_stdio();
    if (!t)
        fatal("Couldn't create TickitTerm: %s", strerror(errno));

    tickit_term_await_started_msec(t, 100);

    tickit_term_get_size(t, &rows, &columns);

    tickit_term_setctl_int(t, TICKIT_TERMCTL_CURSORVIS, 1);
    tickit_term_setctl_int(t, TICKIT_TERMCTL_ALTSCREEN, 1);

    tickit_term_bind_event(t, TICKIT_EV_KEY, handle_input, NULL);
    tickit_term_bind_event(t, TICKIT_EV_RESIZE, handle_resize, NULL);

    for (;;) {
        tickit_term_input_wait_msec(t, 100);
        tickit_term_refresh_size(t);
        
        pthread_mutex_lock(&lock);

        if (atomic_exchange(&should_render, false))
            render_screen(t);

        pthread_mutex_unlock(&lock);

        if (atomic_exchange(&should_pong, false))
            irc_send("PONG");
    }

    return 0;
}
