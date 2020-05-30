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
#include "monitor.h"
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

#define ESCBIT (KEY_MAX + 1)

#if HAVE_BROKEN_ICONV
typedef const char *iconv_input_type;
#else
typedef char *iconv_input_type;
#endif

/* Notifications from signal handler back to event loop */
static volatile sig_atomic_t sigchld, sigwinch;

/* Signal mask on entry */
static sigset_t sigoldmask;

/* True to highlight changes */
static int highlight_changes;

/* True to show line numbers */
static int line_numbers;

static void help(FILE *fp);
static void monitor(const char **cmd, struct timespec interval);
static void setup_signals(void);
static void process_signals(struct state *s);
static void reset_signals(void);
static void discard(int whatever);
static void sighandler_sigchld(int), sighandler_sigwinch(int);
static void setup_curses(void);
static void teardown_curses(void);
static void mainloop(const char **cmd, struct timespec interval);
static void reinvoke(struct state *s, const char **cmd,
                     struct timespec interval);
static void invoke(struct state *s, const char **cmd);
static void process_input(struct state *s);
static void process_keyboard(struct state *s);
static void process_key(struct state *state, int ch);
static void render(struct state *state);
static void pad_line(int y, int x, size_t n);

/* A record of a line in a file */
struct line {
  line(): terminated(false), have_cchars(false) {}
  std::string bytes;           // contents of this line
  std::vector<cchar_t> cchars; // cchar_t representation
  bool terminated;             // true if this line is finished
  bool have_cchars;            // true if cchars is valid

  // Return a pointer to the bytes of the line.
  // (Not 0-terminated.)
  const char *data() const {
    return bytes.data();
  }

  // Return the byte size of the line (i.e. the size of data()).
  size_t size() const {
    return bytes.size();
  }

  // Append a byte string to the line.
  // Invalidates any previous return from get_cchars().
  void append(const char *s, size_t n) {
    if(n) {
      bytes.append(s, n);
      have_cchars = false;
    }
  }

  // Get a reference to the cchar representation of the line
  // (possibly computing it).
  const std::vector<cchar_t> &get_cchars() {
    // Check for a cached copy
    if(!have_cchars) {
      // Keep an iconv handle around indefinitely
      static iconv_t cd = (iconv_t)-1;
      if(cd == (iconv_t)-1)
        if((cd = iconv_open("WCHAR_T", nl_langinfo(CODESET))) == (iconv_t)-1)
          fatal(errno, "iconv_open");
      // Convert the bytes representation to a sequence of code points.
      assert(sizeof(wchar_t) == 4); // sanity check
      std::wstring wchars;
      iconv_input_type in = (iconv_input_type)bytes.data();
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
          case EILSEQ:  // invalid sequence
            escape = 1; // escape one byte and pick up after that
            break;
          case EINVAL:       // incomplete sequence
            escape = inleft; // escape the whole sequence
            break;
          case E2BIG:   // words[] not big enough
            escape = 0; // come back round next time
            break;
          default: fatal(errno, "iconv");
          }
          // Use C-like octal escapes for anything that could not be converted
          assert(inleft >= escape);
          while(escape > 0) {
            swprintf(words, sizeof words / sizeof *words, L"\\%03o",
                     (unsigned char)*in);
            wchars.append(words);
            ++in;
            --inleft;
          }
        }
      }
      // Convert wchars to cchars
      cchars.clear();
      cchars.reserve(wchars.size());
      size_t pos = 0, limit = wchars.size(), column = 0;
      while(pos < limit) {
        wchar_t chars[CCHARW_MAX + 1];
        cchar_t cc;
        size_t n = 0;
        wchar_t wch = wchars[pos];
        // Expand tabs
        if(wch == L'\t') {
          static int tabsize;
          if(!tabsize) {
            const char *e = getenv("TABSIZE");
            if(!e || (tabsize = atoi(e)) <= 0)
              tabsize = 8;
          }
          chars[0] = L' ';
          chars[1] = 0;
          if(setcchar(&cc, chars, 0 /*TODO*/, 0, NULL) == ERR)
            fatal(0, "setcchar failed");
          do {
            cchars.push_back(cc);
            ++column;
          } while(column % tabsize != 0);
          ++pos;
          continue;
        }
        // Escape control characters and other such junk
        const int char_width = wcwidth(wch);
        if(wch == 0 || char_width == -1) {
          wchar_t buffer[16];
          if(wch < 0x80)
            swprintf(buffer, sizeof buffer / sizeof buffer[0], L"\\%03o",
                     (unsigned)wch);
          else if(wch < 0x10000)
            swprintf(buffer, sizeof buffer / sizeof buffer[0], L"\\u%04x",
                     (unsigned)wch);
          else
            swprintf(buffer, sizeof buffer / sizeof buffer[0], L"\\U%08x",
                     (unsigned)wch);
          for(size_t m = 0; buffer[m]; ++m) {
            chars[0] = buffer[m];
            chars[1] = 0;
            if(setcchar(&cc, chars, 0 /*TODO*/, 0, NULL) == ERR)
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
        if(setcchar(&cc, chars, 0 /*TODO*/, 0, NULL) == ERR)
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
  /* Create a file with a given expiry interval
   * If hint is present, it is used to size the lines
   * array, to avoid lots of copying and reallocation in the future.
   */
  file(struct timespec interval, file *hint = nullptr):
      expires(time_monotonic() + interval) {
    size_t initial_lines = 64;
    if(hint) {
      size_t hint_lines = hint->lines.size();
      if(hint_lines > initial_lines)
        initial_lines = hint_lines;
    }
    lines.reserve(initial_lines);
  }

  struct timespec expires; // when this file expires
  std::vector<line> lines; // contents of file

  size_t size() const {
    return lines.size();
  }

  static line dummy;

  /* Find a line. Returns a dummy empty line if you run off the end. */
  line &at(size_t index) {
    if(index < lines.size())
      return lines.at(index);
    else
      return dummy;
  }

  /* Find the last line. Returns a dummy empty line if the file is empty. */
  line &last() {
    return lines.at(lines.size() - 1);
  }

  /* Append arbitrary data */
  void append(const char *s, size_t n) {
    size_t l;
    const char *e;

    while(n > 0) {
      // Do we need a new line?
      if(lines.size() == 0 || last().terminated)
        lines.resize(lines.size() + 1);
      if(*s == '\n') {
        // Newline character, mark the current line as complete.
        last().terminated = true;
        l = 1;
      } else {
        // Bulk-add non-newline characters.
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
    return time_monotonic() >= expires;
  }
};

line file::dummy;

/* State of the event loop */
struct state {
  size_t xo;              /* scrolling X offset */
  size_t yo;              /* scrolling Y offset */
  struct file *previous;  /* previously displayed output or NULL */
  struct file *displayed; /* currently displayed output */
  struct file *reading;   /* currently reading output; could = displayed */
  int done;               /* set by 'q' */
  int render;             /* set to redraw after events processed */
  pid_t pid;              /* subprocess ID or -1 */
  int fd;                 /* input from current process or -1 */
  int status;             /* subprocess status or -1 */
  int escaped;            /* set after ESC key pressed */
  struct timespec clock_expires; /* time at which clock display goes stale */
};

/* Signals handled through the pipe */
static std::pair<int, void (*)(int)> signals[] = {
    {SIGCHLD, sighandler_sigchld}, {SIGWINCH, sighandler_sigwinch}};

enum {
  OPT_HELP = 256,
  OPT_VERSION,
};

static const struct option options[] = {
    {"help", no_argument, 0, OPT_HELP},
    {"version", no_argument, 0, OPT_VERSION},
    {"interval", required_argument, 0, 'n'},
    {"line-numbers", no_argument, 0, 'N'},
    {"shell", no_argument, 0, 's'},
    {"highlight", no_argument, 0, 'h'},
    {0, 0, 0, 0},
};

int main(int argc, char **argv) {
  int n;
  char *e;
  double interval = 1.0;
  double interval_int, interval_frac;
  struct timespec interval_ts;
  int shell = 0;

  if(!setlocale(LC_ALL, ""))
    fatal(errno, "setlocale");
  while((n = getopt_long(argc, argv, "+n:sNh", options, NULL)) >= 0) {
    switch(n) {
    case OPT_HELP: help(stdout); return 0;
    case OPT_VERSION: puts(PACKAGE_VERSION); return 0;
    case 'h': highlight_changes = 1; break;
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
    case 'N': line_numbers = 1; break;
    case 's': shell = 1; break;
    default: return 1;
    }
  }
  if(optind >= argc) {
    help(stderr);
    return 1;
  }
  setup_signals();
  interval_frac = modf(interval, &interval_int);
  interval_ts.tv_sec = floor(interval_int);
  interval_ts.tv_nsec = floor(interval_frac * 1.0E9);
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
    monitor(cmd, interval_ts);
  } else
    monitor((const char **)argv + optind, interval_ts);
  return 0;
}

/* Display usage message */
static void help(FILE *fp) {
  fprintf(fp, "Usage:\n"
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
static void monitor(const char **cmd, struct timespec interval) {
  setup_curses();
  mainloop(cmd, interval);
  teardown_curses();
}

static void set_fd(fd_set &rfds, int fd, int &maxfd) {
  if(fd >= 0) {
    FD_SET(fd, &rfds);
    if(fd > maxfd)
      maxfd = fd;
  }
}

/* Monitor a command */
static void mainloop(const char **cmd, struct timespec interval) {
  struct timespec timeout;
  struct timespec reinvoke_left, clock_left;
  struct state s[1];
  fd_set rfds;

  memset(s, 0, sizeof *s);
  s->fd = -1;
  s->pid = -1;
  s->status = -1;
  FD_ZERO(&rfds);
  while(!s->done) {
    /* Start a new subprocess if the old output has gone stale */
    bool stale = false;
    if(!s->reading)
      stale = true;
    else if(s->reading->out_of_date()) {
      // If the subprocess is slow, give it extra time.
      //
      // If output trickles out then you'll still never see the later bits;
      // you have to manually set a long interval.
      if(s->fd == -1 || s->reading->size() > 0)
        stale = true;
    }
    if(stale)
      reinvoke(s, cmd, interval);
    assert(s->reading);
    // Make sure there is something to display
    if(!s->displayed)
      s->displayed = s->reading;
    /* File descriptors to monitor */
    int maxfd = -1;
    set_fd(rfds, s->fd, maxfd);
    set_fd(rfds, 0, maxfd);
    /* Figure out maximum timeout */
    clock_left =
        s->clock_expires - time_realtime(); // Time before clock advances
    reinvoke_left = s->reading->expires
                    - time_monotonic(); // Time before re-running program
    timeout = clock_left < reinvoke_left
                  ? clock_left
                  : reinvoke_left; // Time before anything happens
    if(timeout.tv_sec >= 0) {
      /* Wait for something to happen */
      if(pselect(maxfd + 1, &rfds, NULL, NULL, &timeout, &sigoldmask) < 0) {
        switch(errno) {
        case EINTR:
        case EAGAIN: break;
        default: fatal(errno, "pselect");
        }
      }
    }
    /* Process events */
    s->render = 0;
    process_signals(s);
    if(s->fd >= 0 && FD_ISSET(s->fd, &rfds)) {
      int sfd = s->fd;
      process_input(s);
      FD_CLR(sfd, &rfds);
    }
    if(FD_ISSET(0, &rfds))
      process_keyboard(s);
    if(!s->render && time_realtime() >= s->clock_expires)
      s->render = 1;
    /* Redraw if anything important has changed */
    if(s->render)
      render(s);
  }
  if(s->reading && s->reading != s->displayed)
    delete s->reading;
  delete s->displayed;
  delete s->previous;
}

/* Command invocation ------------------------------------------------------ */

/* Invoke the command and prepare to capture its output */
static void reinvoke(struct state *s, const char **cmd,
                     struct timespec interval) {
  // Stop reading the current output, if it's being slow
  if(s->fd >= 0)
    close(s->fd);
  // If we never promoted the current reading file to display, discard it
  if(s->reading && s->reading != s->displayed)
    delete s->reading;
  // Start gathering a new current output
  s->reading = new file(interval, s->displayed);
  invoke(s, cmd);
}

/* Invoke the command */
static void invoke(struct state *s, const char **cmd) {
  int p[2];
  static int nullfd = -1;
  pid_t pid;

  assert(cmd);
  // stdin will be /dev/null
  if(nullfd < 0 && (nullfd = open(_PATH_DEVNULL, O_RDONLY)) < 0)
    fatal(errno, _PATH_DEVNULL);
  // stdout and stderr will be a pipe back to us
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
  default: break;
  case -1: fatal(errno, "fork");
  }
  if(close(p[1]) < 0)
    fatal(errno, "close");
  s->fd = p[0];
  s->pid = pid;
  s->status = -1;
}

/* Process input from the command */
static void process_input(struct state *s) {
  char buffer[4096];
  int n;
  assert(s->fd >= 0);
  while((n = read(s->fd, buffer, sizeof buffer)) > 0) {
    s->reading->append(buffer, n);
    // Now that we have some data, promote the current reading file to be
    // displayed
    if(s->reading != s->displayed) {
      delete s->previous;
      s->previous = s->displayed;
      s->displayed = s->reading;
    }
    // Something has changed, so update the display
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
  case 2: /* ^B */
  case KEY_LEFT:
    if(s->xo)
      --s->xo;
    break;
  case 6: /* ^F */
  case KEY_RIGHT: ++s->xo; break;
  case 16: /* ^P */
  case KEY_UP:
    if(s->yo)
      --s->yo;
    break;
  case 14: /* ^N */
  case KEY_DOWN:
    if(s->yo + 1 < s->displayed->size())
      ++s->yo;
    break;
  case KEY_PPAGE:
    getmaxyx(stdscr, height, width);
    discard(width); /* quieten compiler */
    if(height >= 2) {
      if(s->yo > (unsigned)height - 2)
        s->yo -= height - 2;
      else
        s->yo = 0;
    }
    break;
  case KEY_NPAGE:
    getmaxyx(stdscr, height, width);
    discard(width); /* quieten compiler */
    if(height >= 2) {
      s->yo += height - 2;
      if(s->yo + 1 >= s->displayed->size())
        s->yo = s->displayed->size() - 1;
    }
    break;
  case 1: /* ^A */ s->xo = 0; break;
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
  case 'Q': s->done = 1; break;
  }
  if(s->xo != oxo || s->yo != oyo)
    s->render = 1;
}

/* Drawing ----------------------------------------------------------------- */

/* Redraw the display */
static void render(struct state *s) {
  int width, height, y;
  size_t n;
  char sbuf[128];
  char tbuf[128];
  char xbuf[128];
  char footer[sizeof sbuf + sizeof tbuf + sizeof xbuf + 32];
  time_t t;
  int line_digits, left_margin;

  assert(s);
  assert(s->displayed);
  getmaxyx(stdscr, height, width);
  if(width <= 0 || height <= 1)
    return;
  if(erase() == ERR)
    fatal(0, "erase failed");
  if(curs_set(0) == ERR)
    fatal(0, "curs_set");
  if(line_numbers) {
    line_digits = 1 + floor(log10(1 + s->displayed->size()));
    left_margin = line_digits + 1;
  } else {
    line_digits = 0; // quieten compiler
    left_margin = 0;
  }
  for(y = 0; y < height - 1; ++y) {
    // TODO the diff algorithm here is very primitive - any differing
    // lines are highlighted.  This handles insertions and deletions
    // very badly.  Sub-line diff handling would also be nice.
    line &pl = (s->previous ? s->previous : s->displayed)->at(s->yo + y);
    line &cl = s->displayed->at(s->yo + y);
    if(highlight_changes && pl != cl)
      attron(A_REVERSE);
    else
      attroff(A_REVERSE);
    // Prefill with blanks
    pad_line(y, 0, width);
    if(line_numbers && s->yo + y < s->displayed->size()) {
      char line_number_buffer[128];
      snprintf(line_number_buffer, sizeof line_number_buffer, "%*zu ",
               line_digits, s->yo + y + 1);
      if(mvaddnstr(y, 0, line_number_buffer, std::min(left_margin, width))
         == ERR)
        fatal(0, "mvnaddstr failed");
    }
    const std::vector<cchar_t> &cchars = cl.get_cchars();
    size_t pos = 0, limit = cchars.size(), column = 0;
    while(pos < limit) {
      wchar_t wchars[CCHARW_MAX + 1];
      attr_t attrs;
      short color_pair;
      if(getcchar(&cchars[pos], wchars, &attrs, &color_pair, NULL) == ERR)
        fatal(0, "getcchar failed");
      int char_width = wcwidth(wchars[0]);
      if(char_width < 0)
        char_width = 1; // TODO blech
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
  s->clock_expires.tv_sec = t + 1;
  s->clock_expires.tv_nsec = 0;
  if(strftime(tbuf, sizeof tbuf, "%c", localtime(&t)) == 0)
    tbuf[0] = 0;
  if(s->status >= 0) {
    if(WIFEXITED(s->status))
      snprintf(xbuf, sizeof xbuf, " [%d]", WEXITSTATUS(s->status));
    else if(WIFSIGNALED(s->status)) {
      snprintf(xbuf, sizeof xbuf, " [%s]", strsignal(WTERMSIG(s->status)));
    } else
      snprintf(xbuf, sizeof xbuf, " [%#x?]", (unsigned)s->status);
  } else
    xbuf[0] = 0;
  if(s->fd >= 0)
    if(s->reading->size())
      snprintf(sbuf, sizeof sbuf, "[running]");
    else
      snprintf(sbuf, sizeof sbuf, "[blocked]");
  else
    snprintf(sbuf, sizeof sbuf, "[pausing]");
  snprintf(footer, sizeof footer, "%zu:%zu %s %s%s", s->xo, s->yo, tbuf, sbuf,
           xbuf);
  n = strlen(footer);
  if(n > (unsigned)width)
    n = (unsigned)width;
  if(mvinsnstr(height - 1, 0, footer, n) == ERR)
    fatal(0, "mvinsnstr failed (y=%d n=%zu)", height - 1, n);
  pad_line(height - 1, n, width - n);
  attroff(A_REVERSE);
  if(refresh() == ERR)
    fatal(0, "refresh failed");
}

/* Write n spaces at (y,x) */
static void pad_line(int y, int x, size_t n) {
  static const char padding[] = "                                              "
                                "                                              "
                                "                                  "
                                "                                  ";
  static const size_t padding_max_chunk = (sizeof padding) - 1;
  while(n > 0) {
    size_t this_time = n > padding_max_chunk ? padding_max_chunk : n;
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
  sigset_t sighandled;

  memset(&sa, 0, sizeof sa);
  if(sigemptyset(&sa.sa_mask) < 0)
    fatal(errno, "sigemptyset");
  if(sigemptyset(&sighandled) < 0)
    fatal(errno, "sigemptyset");
  for(auto &s: signals) {
    sa.sa_handler = s.second;
    if(sigaction(s.first, &sa, NULL) < 0)
      fatal(errno, "sigaction");
    if(sigaddset(&sighandled, s.first) < 0)
      fatal(errno, "sigaddset");
  }
  if(sigprocmask(SIG_BLOCK, &sighandled, &sigoldmask) < 0)
    fatal(errno, "sigprocmask");
}

/* Reset signal configuration (used between fork and exec) */
static void reset_signals(void) {
  for(auto &s: signals) {
    if(signal(s.first, SIG_DFL) == SIG_ERR)
      fatal(errno, "signal");
  }
  if(sigprocmask(SIG_SETMASK, &sigoldmask, 0) < 0)
    fatal(errno, "sigprocmask");
}

/* Process signals (in the event loop) */
static void process_signals(struct state *s) {
  struct winsize ws;
  pid_t pid;
  int n;
  if(sigchld) {
    while((pid = waitpid(-1, &n, WNOHANG)) > 0) {
      if(pid == s->pid) {
        s->status = n;
        s->pid = -1;
        s->render = 1;
      }
    }
    sigchld = 0;
  }
  if(sigwinch) {
    if(ioctl(0, TIOCGWINSZ, &ws) < 0)
      fatal(errno, "ioctl TIOCGWINSZ");
    resizeterm(ws.ws_row, ws.ws_col);
    s->render = 1;
    sigwinch = 0;
  }
}

/* Quieten picky compilers */
static void discard(int attribute((unused)) whatever) {}

/* Handle SIGCHLD */
static void sighandler_sigchld(int) {
  sigchld = 1;
}

/* Handle SIGWINCH */
static void sighandler_sigwinch(int) {
  sigwinch = 1;
}

/* Curses setup ------------------------------------------------------------ */

/* Set up curses library */
static void setup_curses(void) {
  if(!initscr())
    fatal(0, "initscr failed");
  onfatal = endwin;
  if(cbreak() == ERR) /* Read keys as they are pressed */
    fatal(0, "cbreak failed");
  if(noecho() == ERR) /* Suppress echoing of type keys */
    fatal(0, "noecho failed");
  if(nonl() == ERR) /* Suppress newline translation */
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
