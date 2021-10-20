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
#ifndef MONITOR_H
#define MONITOR_H

#include <config.h>
#include <ctime>
#include <sys/time.h>

extern int (*onfatal)(void);
extern bool forking;
void fatal(int errno_value, const char *fmt, ...) attribute((noreturn));

struct timespec time_monotonic();
struct timespec time_realtime();

#define BILLION (1000 * 1000 * 1000)

inline struct timespec operator+(struct timespec a, struct timespec b) {
  struct timespec r = {a.tv_sec + b.tv_sec, a.tv_nsec + b.tv_nsec};
  while(r.tv_nsec >= BILLION) {
    r.tv_nsec -= BILLION;
    r.tv_sec++;
  }
  return r;
}

inline struct timespec operator-(struct timespec a, struct timespec b) {
  struct timespec r = {a.tv_sec - b.tv_sec, a.tv_nsec - b.tv_nsec};
  while(r.tv_nsec < 0) {
    r.tv_nsec += BILLION;
    r.tv_sec--;
  }
  return r;
}

inline bool operator<(struct timespec a, struct timespec b) {
  if(a.tv_sec < b.tv_sec)
    return true;
  if(a.tv_sec == b.tv_sec && a.tv_nsec < b.tv_nsec)
    return true;
  return false;
}

inline bool operator>(struct timespec a, struct timespec b) {
  return b < a;
}

inline bool operator<=(struct timespec a, struct timespec b) {
  return !(b < a);
}

inline bool operator>=(struct timespec a, struct timespec b) {
  return !(a < b);
}

#endif /* MONITOR_H */

/*
Local Variables:
mode:c++
c-basic-offset:2
comment-column:40
fill-column:79
indent-tabs-mode:nil
End:
*/
