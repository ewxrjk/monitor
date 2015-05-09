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
#include <cassert>
#include <cerrno>
#include <clocale>
#include <cmath>
#include <csignal>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <curses.h>
#include <fcntl.h>
#include <getopt.h>
#include <iconv.h>
#include <langinfo.h>
#include <paths.h>
#include <poll.h>
#include <string>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

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

/* True to show line numbers */
static int line_numbers;

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
static double now(clockid_t c);
static void fatal(int errno_value, const char *fmt, ...);

/* A record of a line in a file */
struct line {
  line(): terminated(false),
          have_cchars(false) {
  }
  std::string bytes;            // contents of this line
  std::vector<cchar_t> cchars;  // cchar_t representation
  bool terminated;              // true if this line is finished
  bool have_cchars;             // true if cchars is valid

  const char *data() const { return bytes.data(); }
  size_t size() const { return bytes.size(); }

  void append(const char *s, size_t n) {
    if(n) {
      bytes.append(s, n);
      have_cchars = false;
    }
  }

  const std::vector<cchar_t> &get_cchars() {
    if(!have_cchars) {
      // Keep an iconv handle around indefinitely
      static iconv_t cd = (iconv_t)-1;
      if(cd == (iconv_t)-1)
        if((cd = iconv_open("WCHAR_T", nl_langinfo(CODESET))) == (iconv_t)-1)
          fatal(errno, "iconv_open");
      assert(sizeof(wchar_t) == 4); // sanity check
      std::wstring wchars;
      char *in = (char *)bytes.data();
      size_t inleft = bytes.size();
      while(inleft > 0) {
        wchar_t words[128];
        char *out = (char *)&words[0];
        size_t outleft = sizeof words;
        size_t rc = iconv(cd, &in, &inleft, &out, &outleft);
        wchars.append(words, ((sizeof words) - outleft) / sizeof(wchar_t));
        if(rc == (size_t)-1) {
          size_t escape;
          switch(errno) {
          case EILSEQ:          // invalid sequence
            escape = 1;         // escape one byte and pick up after that
            break;
          case EINVAL:          // incomplete sequence
            escape = inleft;    // escape the whole sequence
            break;
          case E2BIG:           // words[] not big enough
            escape = 0;         // come back round next time
            break;
          default:
            fatal(errno, "iconv");
          }
          // Use C-like octal escapes for anything that could not be converted
          assert(inleft > escape);
          while(escape > 0) {
            swprintf(words, sizeof words / sizeof *words,
                     L"\\%03o", (unsigned char)*in);
            wchars.append(words);
            ++in;
            --inleft;
          }
        }
      }
      cchars.clear();
      size_t pos = 0, limit = wchars.size(), column = 0;
      while(pos < limit) {
        wchar_t chars[CCHARW_MAX+1];
        cchar_t cc;
        size_t n = 0;
        wchar_t wch = wchars[pos];
        if(wch == L'\t') { // Expand tabs
          static int tabsize;
          if(!tabsize) {
            const char *e = getenv("TABSIZE");
            if(!e || (tabsize = atoi(e)) <= 0)
              tabsize = 8;
          }
          chars[0] = L' ';
          chars[1] = 0;
          if(setcchar(&cc, chars, 0/*TODO*/, 0, NULL) == ERR)
            fatal(0, "setcchar failed");
          do {
            cchars.push_back(cc);
            ++column;
          } while(column % tabsize != 0);
          ++pos;
          continue;
        }
        const int char_width = wcwidth(wch);
        if(wch == 0 || char_width == -1) {  // Control character or junk
          wchar_t buffer[16];
          if(wch < 0x80)
            swprintf(buffer, sizeof buffer / sizeof buffer[0],
                     L"\\%03o", (unsigned)wch);
          else if(wch < 0x10000)
            swprintf(buffer, sizeof buffer / sizeof buffer[0],
                     L"\\u%04x", (unsigned)wch);
          else
            swprintf(buffer, sizeof buffer / sizeof buffer[0],
                     L"\\U%08x", (unsigned)wch);
          for(size_t m = 0; buffer[m]; ++m) {
            chars[0] = buffer[m];
            chars[1] = 0;
            if(setcchar(&cc, chars, 0/*TODO*/, 0, NULL) == ERR)
              fatal(0, "setcchar failed");
            cchars.push_back(cc);
          }
          ++pos;
          continue;
        }
        if(char_width == 0) {
          // Starts with a nonspacing character.  Bodge something up...
          chars[n++] = L' ';
          column += 1;
        } else {
          chars[n++] = wchars[pos++];
          column += char_width;
        }
        while(pos < limit && wchars[pos] && wcwidth(wchars[pos]) == 0) {
          // Combining character sequences that are too long are
          // simply truncated.
          // TODO converting to NFC (if not already there) would provide
          // a bit more room.
          if(n < CCHARW_MAX)
            chars[n++] = wchars[pos];
          ++pos;
        }
        chars[n] = 0;
        if(setcchar(&cc, chars, 0/*TODO*/, 0, NULL) == ERR)
          fatal(0, "setcchar failed");
        cchars.push_back(cc);
        assert(pos > 0);
      }
    }
    return cchars;
  }

  bool operator!=(const line &that) const {
    return bytes != that.bytes;
  }
};

/* An entire file, read from a subprocess */
struct file {
  /* Create a file with a given expiry interval */
  file(double interval) : expires(now(CLOCK_MONOTONIC) + interval) {
  }

  double expires;               // when this file expires
  std::vector<line> lines;      // contents of file

  size_t size() const {
    return lines.size();
  }

  /* Find a line */
  line &at(size_t index) {
    static line dummy;
    if(index < lines.size())
      return lines.at(index);
    else
      return dummy;
  }

  /* Find the last line */
  line &last() {
    return lines.at(lines.size()-1);
  }

  /* Append data */
  void append(const char *s, size_t n) {
    size_t l;
    const char *e;

    while(n > 0) {
      if(lines.size() == 0 || last().terminated)
        lines.push_back(line());
      if(*s == '\n') {
        last().terminated = true;
        l = 1;
      } else {
        if((e = static_cast<const char *>(memchr(s, '\n', n))))
          l = e - s;
        else
          l = n;
        last().append(s, l);
      }
      s += l;
      n -= l;
    }
  }

  /* Return true if this file is out of date */
  bool out_of_date() const {
    return now(CLOCK_MONOTONIC) >= expires;
  }
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

enum {
  OPT_HELP = 256,
  OPT_VERSION,
};

static const struct option options[] = {
  { "help", no_argument, 0, OPT_HELP },
  { "version", no_argument, 0, OPT_VERSION },
  { "interval", required_argument, 0, 'n' },
  { "line-numbers", no_argument, 0, 'N' },
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
  while((n = getopt_long(argc, argv, "+n:sNh",
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
    case 'N':
      line_numbers = 1;
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
    std::string shell_command;
    const char *cmd[4];
    for(n = optind; n < argc; ++n) {
      shell_command += ' ';
      shell_command += argv[n];
    }
    cmd[0] = getenv("SHELL");
    if(!cmd[0])
      cmd[0] = "sh";
    cmd[1] = "-c";
    cmd[2] = shell_command.c_str();
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
          "  -N, --line-numbers      Display line numbers\n"
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
    if(!s->current || s->current->out_of_date())
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
  delete s->current;
  delete s->previous;
}

/* Command invocation ------------------------------------------------------ */

/* Invoke the command and prepare to capture its output */
static void reinvoke(struct state *s, const char **cmd, double interval) {
  delete s->previous;
  if(s->fd >= 0)
    close(s->fd);
  s->previous = s->current;
  s->current = new file(interval);
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
    s->current->append(buffer, n);
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
    if(s->yo + 1 < s->current->size())
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
    if(height >= 2) {
      s->yo += height - 2;
      if(s->yo + 1 >= s->current->size())
        s->yo = s->current->size() - 1;
    }
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
  case 'n':
  case 'N':
    line_numbers = !line_numbers;
    s->render = 1;
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
  size_t n;
  char footer[128];
  char sbuf[128];
  char tbuf[128];
  time_t t;
  int line_digits, left_margin;

  assert(s);
  assert(s->current);
  getmaxyx(stdscr, height, width);
  if(width <= 0 || height <= 1)
    return;
  if(erase() == ERR)
    fatal(0, "erase failed");
  if(curs_set(0) == ERR)
    fatal(0, "curs_set");
  if(line_numbers) {
    line_digits = 1 + floor(log10(1 + s->current->size()));
    left_margin = line_digits + 1;
  } else {
    line_digits = 0;            // quieten compiler
    left_margin = 0;
  }
  for(y = 0; y < height - 1; ++y) {
    // TODO the diff algorithm here is very primitive - any differing
    // lines are highlighted.  This handles insertions and deletions
    // very badly.  Sub-line diff handling would also be nice.
    line &pl = (s->previous ? s->previous : s->current)->at(s->yo + y);
    line &cl = s->current->at(s->yo + y);
    if(highlight_changes && pl != cl)
      attron(A_REVERSE);
    else
      attroff(A_REVERSE);
    // Prefill with blanks
    pad_line(y, 0, width);
    if(line_numbers && s->yo + y < s->current->size()) {
      char line_number_buffer[128];
      snprintf(line_number_buffer, sizeof line_number_buffer,
               "%*zu ", line_digits, s->yo + y + 1);
      if(mvaddnstr(y, 0, line_number_buffer,
                   std::min(left_margin, width)) == ERR)
        fatal(0, "mvnaddstr failed");
    }
    const std::vector<cchar_t> &cchars = cl.get_cchars();
    size_t pos = 0, limit = cchars.size(), column = 0;
    while(pos < limit) {
      wchar_t wchars[CCHARW_MAX+1];
      attr_t attrs;
      short color_pair;
      if(getcchar(&cchars[pos], wchars, &attrs, &color_pair, NULL) == ERR)
        fatal(0, "getcchar failed");
      int char_width = wcwidth(wchars[0]);
      if(char_width < 0)
        char_width = 1;         // TODO blech
      if(column >= s->xo) {
        int x = left_margin + column - s->xo;
        if(x < width) {
          if(mvadd_wch(y, x, &cchars[pos]) == ERR)
            fatal(0, "mvins_wch failed (y=%d x=%d)", y, x);
        } else
          break;
      }
      column += char_width;
      ++pos;
    }
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
  static const char padding[] = "        ";
  while(n > 0) {
    size_t this_time = n > strlen(padding) ? strlen(padding) : n;
    if(mvinsnstr(y, x, padding, this_time) == ERR)
      fatal(0, "mvinsnstr failed (y=%d x=%d n=%zu)", y, x, this_time);
    x += this_time;
    n -= this_time;
  }
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
