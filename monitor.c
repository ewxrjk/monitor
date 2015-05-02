/* This file is part of monitor.
 * Copyright (C) 2015 Richard Kettlewell
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
 * USA
 */
#include <config.h>
#include <assert.h>
#include <curses.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <locale.h>
#include <math.h>
#include <paths.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define ESCBIT (KEY_MAX+1)

/* Called to clean up before reporting an fatal error */
static int (*onfatal)(void);

/* Called to exit the process */
static void (*terminate)(int) attribute((noreturn)) = exit;

/* Pipe from signal handler back to event loop */
static int sigpipe[2];

/* Signal mask on entry */
static sigset_t sigoldmask;

/* True to highlight changes */
static int highlight_changes;

/* A record of a line in a file */
struct line {
  size_t space;                 /* space in bytes[] */
  size_t len;                   /* how much of bytes[] actually used */
  char *bytes;                  /* content of line (including \n) */
};

/* An entire file, read from a subprocess */
struct file {
  double expires;               /* when this file expires */
  size_t nslots;                /* number of available entries in lines[] */
  size_t nlines;                /* number of used entries in lines[] */
  struct line *lines;           /* content of file (so far) */
};

/* State of the event loop */
struct state {
  size_t xo;                    /* scrolling X offset */
  size_t yo;                    /* scrolling Y offset */
  struct file *previous;        /* previous file output or NULL */
  struct file *current;         /* current file output */
  int done;                     /* set by 'q' */
  int render;                   /* set to redraw after events processed */
  pid_t pid;                    /* subprocess ID or -1 */
  int fd;                       /* input from current process or -1 */
  int status;                   /* subprocess status or -1 */
  int escaped;                  /* set after ESC key pressed */
  double clock_expires;         /* time at which clock display goes stale */
};

/* Signals handled through the pipe */
static const int signals[] = { SIGCHLD, SIGWINCH };

static void help(FILE *fp);
static void monitor(const char **cmd, double interval);
static void setup_signals(void);
static void process_signals(struct state *s);
static void reset_signals(void);
static void discard(int whatever);
static void sighandler(int sig);
static void setup_curses(void);
static void teardown_curses(void);
static void mainloop(const char **cmd, double interval);
static void reinvoke(struct state *s, const char **cmd, double interval);
static void invoke(struct state *s, const char **cmd);
static void process_input(struct state *s);
static void process_keyboard(struct state *s);
static void process_key(struct state *state, int ch);
static void render(struct state *state);
static void pad_line(int y, int x, size_t n);
static struct file *file_new(double interval);
static void file_free(struct file *f);
static void file_append(struct file *f, const char *s, size_t n);
static int file_out_of_date(const struct file *f);
static const struct line *file_line(const struct file *f, size_t line);
static void line_append(struct line *l, const char *s, size_t n);
static void line_free(struct line *l);
static int line_equal(const struct line *a, const struct line *b);
static double now(clockid_t c);
static void fatal(int errno_value, const char *fmt, ...);

enum {
  OPT_HELP = 256,
  OPT_VERSION,
};

static const struct option options[] = {
  { "help", no_argument, 0, OPT_HELP },
  { "version", no_argument, 0, OPT_VERSION },
  { "interval", required_argument, 0, 'n' },
  { "shell", no_argument, 0, 's' },
  { "highlight", no_argument, 0, 'h' },
  { 0, 0, 0, 0 },
};

int main(int argc, char **argv) {
  int n;
  char *e;
  double interval = 1.0;
  int shell = 0;

  if(!setlocale(LC_ALL, ""))
    fatal(errno, "setlocale");
  while((n = getopt_long(argc, argv, "+n:sh",
                         options, NULL)) >= 0) {
    switch(n) {
    case OPT_HELP:
      help(stdout);
      return 0;
    case OPT_VERSION:
      puts(PACKAGE_VERSION);
      return 0;
    case 'h':
      highlight_changes = 1;
      break;
    case 'n':
      errno = 0;
      interval = strtod(optarg, &e);
      if(errno)
        fatal(errno, "invalid interval '%s'", optarg);
      if(*e || e == optarg)
        fatal(0, "invalid interval '%s': must be a number", optarg);
      if(interval < 0)
        fatal(0, "invalid interval '%s': must be positive", optarg);
      break;
    case 's':
      shell = 1;
      break;
    default:
      return 1;
    }
  }
  if(optind >= argc) {
    help(stderr);
    return 1;
  }
  setup_signals();
  if(shell) {
    struct line l;
    static const char *cmd[4];
    memset(&l, 0, sizeof l);
    for(n = optind; n < argc; ++n) {
      if(n != optind)
        line_append(&l, " ", 1);
      line_append(&l, argv[n], strlen(argv[n]));
    }
    line_append(&l, "", 1);
    cmd[0] = getenv("SHELL");
    if(!cmd[0])
      cmd[0] = "sh";
    cmd[1] = "-c";
    cmd[2] = l.bytes;
    cmd[3] = NULL;
    monitor(cmd, interval);
  } else
    monitor((const char **)argv + optind, interval);
  return 0;
}

/* Display usage message */
static void help(FILE *fp) {
  fprintf(fp,
          "Usage:\n"
          "  monitor [OPTIONS] [--] COMMAND [ARG ...]\n"
          "Options:\n"
          "  -h, --highlight         Highlight changed lines\n"
          "  -n, --interval SECONDS  Delay between invocations of command\n"
          "  -s, --shell             Run command via the shell\n"
          "  --help                  Display usage message\n"
          "  --version               Display version string\n");
}

/* Main loop --------------------------------------------------------------- */

/* Set up curses, monitor a command, and tear down curses */
static void monitor(const char **cmd, double interval) {
  setup_curses();
  mainloop(cmd, interval);
  teardown_curses();
}

/* Monitor a command */
static void mainloop(const char **cmd, double interval) {
  struct pollfd pfds[3];
  struct timespec timeout;
  double reinvoke_left, clock_left, left, left_sec, left_nsec;
  struct state s[1];

  assert(interval > 0);
  memset(s, 0, sizeof *s);
  s->fd = -1;
  s->pid = -1;
  s->status = -1;
  while(!s->done) {
    /* Start a new subprocess if the old output has gone stale */
    if(file_out_of_date(s->current))
      reinvoke(s, cmd, interval);
    assert(s->current);
    /* File descriptors to monitor */
    memset(pfds, 0, sizeof pfds);
    pfds[0].fd = sigpipe[0];
    pfds[0].events = POLLIN;
    pfds[1].fd = s->fd;
    pfds[1].events = POLLIN;
    pfds[2].fd = 0;
    pfds[2].events = POLLIN;
    /* Figure out maximum timeout */
    clock_left = s->clock_expires - now(CLOCK_REALTIME);
    reinvoke_left = s->current->expires - now(CLOCK_MONOTONIC);
    left = clock_left < reinvoke_left ? clock_left : reinvoke_left;
    if(left < 0)
      left = 0;
    left_nsec = modf(left, &left_sec);
    timeout.tv_sec = floor(left_sec);
    timeout.tv_nsec = floor(left_nsec * 1.0E9);
    /* Wait for someting to happen */
    if(ppoll(pfds, sizeof pfds / sizeof *pfds, &timeout, &sigoldmask) < 0) {
      if(errno == EINTR || errno == EAGAIN)
        continue;
      fatal(errno, "ppoll");
    }
    /* Process events */
    s->render = 0;
    if(pfds[0].revents & (POLLIN|POLLHUP))
      process_signals(s);
    if(pfds[1].revents & (POLLIN|POLLHUP))
      process_input(s);
    if(pfds[2].revents & (POLLIN|POLLHUP))
      process_keyboard(s);
    if(!s->render && now(CLOCK_REALTIME) >= s->clock_expires)
      s->render = 1;
    /* Redraw if anything important has changed */
    if(s->render)
      render(s);
  }
  file_free(s->current);
  file_free(s->previous);
}

/* Command invocation ------------------------------------------------------ */

/* Invoke the command and prepare to capture its output */
static void reinvoke(struct state *s, const char **cmd, double interval) {
  file_free(s->previous);
  if(s->fd >= 0)
    close(s->fd);
  s->previous = s->current;
  s->current = file_new(interval);
  invoke(s, cmd);
}

/* Invoke the command */
static void invoke(struct state *s, const char **cmd) {
  int p[2];
  static int nullfd = -1;
  pid_t pid;

  assert(cmd);
  if(nullfd < 0 && (nullfd = open(_PATH_DEVNULL, O_RDONLY)) < 0)
    fatal(errno, _PATH_DEVNULL);
  if(pipe(p) < 0)
    fatal(errno, "pipe");
  switch(pid = fork()) {
  case 0:
    onfatal = NULL;
    terminate = _exit;
    if(dup2(p[1], 2) < 0 || dup2(p[1], 1) < 0 || dup2(nullfd, 0) < 0)
      fatal(errno, "dup2");
    if(close(p[0]) < 0 || close(p[1]) < 0 || close(nullfd) < 0)
      fatal(errno, "close");
    reset_signals();
    if(execvp(cmd[0], (char **)cmd) < 0)
      fatal(errno, "execvp %s", cmd[0]);
    fatal(0, "execvp unexpectedly returned");
  default:
    break;
  case -1:
    fatal(errno, "fork");
  }
  if(close(p[1]) < 0)
    fatal(errno, "close");
  s->fd = p[0];
  s->pid = pid;
}

/* Process input from the command */
static void process_input(struct state *s) {
  char buffer[4096];
  int n;
  assert(s->fd >= 0);
  while((n = read(s->fd, buffer, sizeof buffer)) > 0) {
    file_append(s->current, buffer, n);
    s->render = 1;
  }
  if(n < 0) {
    if(errno != EINTR && errno != EAGAIN)
      fatal(errno, "read");
  } else if(n == 0) {
    close(s->fd);
    s->fd = -1;
  }
}

/* Keyboard input ---------------------------------------------------------- */

/* Process keyboard input */
static void process_keyboard(struct state *s) {
  int ch;

  if((ch = getch()) != ERR) {
    if(s->escaped) {
      process_key(s, ch | ESCBIT);
      s->escaped = 0;
    } else if(ch == 27)
      s->escaped = 1;
    else
      process_key(s, ch);
  }
}

/* Process a single key */
static void process_key(struct state *s, int ch) {
  int width, height;
  size_t oxo = s->xo, oyo = s->yo;
  switch(ch) {
  case 2:                       /* ^B */
  case KEY_LEFT:
    if(s->xo)
      --s->xo;
    break;
  case 6:                       /* ^F */
  case KEY_RIGHT:
    ++s->xo;
    break;
  case 16:                      /* ^P */
  case KEY_UP:
    if(s->yo)
      --s->yo;
    break;
  case 14:                      /* ^N */
  case KEY_DOWN:
    ++s->yo;
    break;
  case KEY_PPAGE:
    getmaxyx(stdscr, height, width);
    discard(width);             /* quieten compiler */
    if(height >= 2) {
      if(s->yo > (unsigned)height - 2)
        s->yo -= height - 2;
      else
        s->yo = 0;
    }
    break;
  case KEY_NPAGE:
    getmaxyx(stdscr, height, width);
    discard(width);             /* quieten compiler */
    if(height >= 2)
      s->yo += height - 2;
    break;
  case 1:                       /* ^A */
    s->xo = 0;
    break;
  case KEY_HOME:
    s->xo = 0;
    s->yo = 0;
    break;
  case 12:
    if(redrawwin(stdscr) == ERR)
      fatal(0, "redrawwin failed");
    break;
  case 'q':
  case 'Q':
    s->done = 1;
    break;
  }
  if(s->xo != oxo || s->yo != oyo)
    s->render = 1;
}

/* Drawing ----------------------------------------------------------------- */

/* Redraw the display */
static void render(struct state *s) {
  int width, height, y;
  const char *str;
  size_t n;
  char footer[128];
  char sbuf[128];
  char tbuf[128];
  time_t t;

  assert(s);
  assert(s->current);
  getmaxyx(stdscr, height, width);
  if(width <= 0 || height <= 1)
    return;
  if(erase() == ERR)
    fatal(0, "erase failed");
  if(curs_set(0) == ERR)
    fatal(0, "curs_set");
  for(y = 0; y < height - 1; ++y) {
    // TODO the diff algorithm here is very primitive - any differing
    // lines are highlighted.  This handles insertions and deletions
    // very badly.  Sub-line diff handling would also be nice.
    const struct line *pl = file_line(s->previous ? s->previous : s->current,
                                      s->yo + y);
    const struct line *cl = file_line(s->current, s->yo + y);
    if(highlight_changes && !line_equal(pl, cl))
      attron(A_REVERSE);
    else
      attroff(A_REVERSE);
    // TODO this is junk for non-ASCII input.
    if(s->xo > cl->len) {
      str = cl->bytes;
      n = 0;
    } else {
      str = cl->bytes + s->xo;
      n = cl->len - s->xo;
    }
    if(n > 0 && str[n-1] == '\n')
      --n;
    if(n > (unsigned)width)
      n = width;
    if(n)
      if(mvinsnstr(y, 0, str, n) == ERR)
        fatal(0, "mvinsnstr failed (y=%d n=%zu)", y, n);
    pad_line(y, n, width - n);
  }
  attron(A_REVERSE);
  time(&t);
  s->clock_expires = t + 1;
  if(strftime(tbuf, sizeof tbuf, "%c", localtime(&t)) == 0)
    tbuf[0] = 0;
  if(s->status >= 0) {
    if(WIFEXITED(s->status))
      snprintf(sbuf, sizeof sbuf, " [%d]", WEXITSTATUS(s->status));
    else if(WIFSIGNALED(s->status)) {
      snprintf(sbuf, sizeof sbuf, " [%s%s]",
               strsignal(WTERMSIG(s->status)),
               WCOREDUMP(s->status) ? " (core)" : "");
    } else
      snprintf(sbuf, sizeof sbuf, " [%#x?]", (unsigned)s->status);
  } else if(s->fd >= 0)
    snprintf(sbuf, sizeof sbuf, " [running]");
  else
    sbuf[0] = 0;
  snprintf(footer, sizeof footer,
           "%zu:%zu%s %s", s->xo, s->yo, sbuf, tbuf);
  n = strlen(footer);
  if(n > (unsigned)width)
    n = (unsigned)width;
  if(mvinsnstr(height-1, 0, footer, n) == ERR)
    fatal(0, "mvinsnstr failed (y=%d n=%zu)", height-1, n);
  pad_line(height - 1, n, width - n);
  attroff(A_REVERSE);
  if(refresh() == ERR)
    fatal(0, "refresh failed");
}

/* Write n spaces at (y,x) */
static void pad_line(int y, int x, size_t n) {
  static const char padding[8] = "        ";
  while(n > 0) {
    size_t this_time = n > sizeof padding ? sizeof padding : n;
    if(mvinsnstr(y, x, padding, this_time) == ERR)
      fatal(0, "mvinsnstr failed (y=%d x=%d n=%zu)", y, x, this_time);
    x += this_time;
    n -= this_time;
  }
}

/* File contents handling -------------------------------------------------- */

/* Create a new file */
static struct file *file_new(double interval) {
  struct file *f = calloc(sizeof *f, 1);
  if(!f)
    fatal(errno, "calloc");
  f->expires = now(CLOCK_MONOTONIC) + interval;
  return f;
}

/* Destroy a file */
static void file_free(struct file *f) {
  if(f) {
    size_t n = 0;
    for(n = 0; n < f->nlines; ++n)
      line_free(&f->lines[n]);
    free(f->lines);
    f->nslots = 0;
    f->nlines = 0;
    f->lines = 0;
    free(f);
  }
}

/* Append some data to a file */
static void file_append(struct file *f, const char *s, size_t n) {
  char *e;
  size_t l;
  assert(f);
  while(n > 0) {
    if(f->nlines == 0
     || (f->nlines > 0
         && f->lines[f->nlines-1].len > 0
         && f->lines[f->nlines-1].bytes[f->lines[f->nlines-1].len-1] == '\n')) {
      if(f->nlines == f->nslots) {
        f->nslots = f->nslots ? 2 * f->nslots : 32;
        if(!f->nslots || !(f->lines = realloc(f->lines,
                                              f->nslots * sizeof(*f->lines))))
          fatal(errno, "realloc");
      }
      memset(&f->lines[f->nlines], 0, sizeof f->lines[f->nlines]);
      ++f->nlines;
    }
    if((e = memchr(s, '\n', n)))
      l = (e - s) + 1;
    else
      l = n;
    line_append(&f->lines[f->nlines-1], s, l);
    n -= l;
    s += l;
  }
}

/* Return nonzero if a file is out of date */
static int file_out_of_date(const struct file *f) {
  return f == NULL || now(CLOCK_MONOTONIC) >= f->expires;
}

/* Find a line in a file */
static const struct line *file_line(const struct file *f, size_t line) {
  static struct line dummy_line;
  assert(f);
  if(line < f->nlines)
    return &f->lines[line];
  else
    return &dummy_line;
}

/* Append data to a line */
static void line_append(struct line *l, const char *s, size_t n) {
  /* TODO special handling for tabs */
  assert(l);
  if(n > l->space - l->len) {
    l->space = l->space ? 2 * l->space : 16;
    while(l->space && n > l->space - l->len)
      l->space *= 2;
    if(!l->space || !(l->bytes = realloc(l->bytes, l->space)))
      fatal(errno, "realloc");
  }
  memcpy(l->bytes + l->len, s, n);
  l->len += n;
}

/* Free a line */
static void line_free(struct line *l) {
  assert(l);
  free(l->bytes);
  l->space = 0;
  l->len = 0;
  l->bytes = 0;
}

/* Return nonzero if two lines are equal */
static int line_equal(const struct line *a, const struct line *b) {
  assert(a);
  assert(b);
  if(a->len == b->len)
    return !memcmp(a->bytes, b->bytes, a->len);
  else
    return 0;
}

/* Signal handling --------------------------------------------------------- */

/* Set up signal handling */
static void setup_signals(void) {
  struct sigaction sa;
  int n;
  size_t i;
  sigset_t sighandled;

  if(pipe(sigpipe) < 0)
    fatal(errno, "pipe");
  for(i = 0; i < 2; ++i) {
    if((n = fcntl(sigpipe[i], F_GETFL)) < 0)
      fatal(errno, "fcntl");
    if(fcntl(sigpipe[i], F_SETFL, n | O_NONBLOCK) < 0)
      fatal(errno, "fcntl");
    if((n = fcntl(sigpipe[i], F_GETFD)) < 0)
      fatal(errno, "fcntl");
    if(fcntl(sigpipe[i], F_SETFD, n | FD_CLOEXEC) < 0)
      fatal(errno, "fcntl");
  }
  sa.sa_handler = sighandler;
  sa.sa_flags = 0;
  if(sigemptyset(&sa.sa_mask) < 0)
    fatal(errno, "sigemptyset");
  if(sigemptyset(&sighandled) < 0)
    fatal(errno, "sigemptyset");
  for(i = 0; i < sizeof signals / sizeof *signals; ++i) {
    if(sigaction(signals[i], &sa, NULL) < 0)
      fatal(errno, "sigaction");
    if(sigaddset(&sighandled, signals[i]) < 0)
      fatal(errno, "sigaddset");
  }
  if(sigprocmask(SIG_BLOCK, &sighandled, &sigoldmask) <0)
    fatal(errno, "sigprocmask");
}

/* Reset signal configuration (used between fork and exec) */
static void reset_signals(void) {
  size_t i;

  for(i = 0; i < sizeof signals / sizeof *signals; ++i) {
    if(signal(signals[i], SIG_DFL) == SIG_ERR)
      fatal(errno, "signal");
  }
  if(sigprocmask(SIG_SETMASK, &sigoldmask, 0) < 0)
    fatal(errno, "sigprocmask");
}

/* Process signals (in the event loop) */
static void process_signals(struct state *s) {
  unsigned char sig;
  struct winsize ws;
  int n;
  pid_t pid;
  while((n = read(sigpipe[0], &sig, 1)) > 0) {
    switch(sig) {
    case SIGCHLD:
      while((pid = waitpid(-1, &n, WNOHANG)) > 0) {
        if(pid == s->pid) {
          s->status = n;
          s->pid = -1;
          s->render = 1;
        }
      }
      break;
    case SIGWINCH:
      if(ioctl(0, TIOCGWINSZ, &ws) < 0)
        fatal(errno, "ioctl TIOCGWINSZ");
      resizeterm(ws.ws_row, ws.ws_col);
      s->render = 1;
      break;
    default:
      fatal(0, "unexpected signal %d", sig);
    }
  }
  if(n < 0) {
    if(errno == EINTR || errno == EAGAIN)
      return;
    fatal(errno, "read from sigpipe");
  } else if(n == 0)
    fatal(0, "unexpected EOF from sigpipe");
}

/* Quieten picky compilers */
static void discard(int attribute((unused)) whatever) { }

/* Handle a signal directly */
static void sighandler(int sig) {
  unsigned char sigc = sig;
  int save_errno = errno;
  discard(write(sigpipe[1], &sigc, 1));
  errno = save_errno;
}

/* Curses setup ------------------------------------------------------------ */

/* Set up curses library */
static void setup_curses(void) {
  if(!initscr())
    fatal(0, "initscr failed");
  onfatal = endwin;
  if(cbreak() == ERR)           /* Read keys as they are pressed */
    fatal(0, "cbreak failed");
  if(noecho() == ERR)           /* Suppress echoing of type keys */
    fatal(0, "noecho failed");
  if(nonl() == ERR)             /* Suppress newline translation */
    fatal(0, "nonl failed");
  if(intrflush(stdscr, FALSE) == ERR) /* Flush output on ^C */
    fatal(0, "initrflush failed");
  if(keypad(stdscr, TRUE) == ERR) /* Enable keypad support */
    fatal(0, "keypad failed");
  if(nodelay(stdscr, TRUE) == ERR) /* getch() shouldn't block */
    fatal(0, "nodelay failed");
}

/* Close down curses library */
static void teardown_curses(void) {
  onfatal = NULL;
  if(endwin() == ERR)
    fatal(0, "endwin failed");
}

/* Miscellaneous ----------------------------------------------------------- */

/* Return the time according to some system clock */
static double now(clockid_t c) {
  struct timespec ts;
  if(clock_gettime(c, &ts) < 0)
    fatal(errno, "clock_gettime %#x", (unsigned)c);
  return ts.tv_sec + ts.tv_nsec / 1.0E9;
}

/* Report an error and terminate */
static void fatal(int errno_value, const char *fmt, ...) {
  va_list ap;

  assert(fmt);
  if(onfatal)
    onfatal();
  va_start(ap, fmt);
  fprintf(stderr, "ERROR: ");
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  if(errno_value)
    fprintf(stderr, ": %s\n", strerror(errno_value));
  else
    fprintf(stderr, "\n");
  terminate(1);
}
