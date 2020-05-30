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
#include <cerrno>

#if HAVE_CLOCK_GETTIME
static struct timespec time_posix(clockid_t c) {
  struct timespec ts;
  if(clock_gettime(c, &ts) < 0)
    fatal(errno, "clock_gettime %#x", (unsigned)c);
  return ts;
}
#endif

struct timespec time_monotonic() {
#if HAVE_CLOCK_GETTIME
  return time_posix(CLOCK_MONOTONIC);
#else
#error port me
#endif
}

struct timespec time_realtime() {
#if HAVE_CLOCK_GETTIME
  return time_posix(CLOCK_REALTIME);
#else
  struct timeval tv;
  if(gettimeofday(&tv, NULL) < 0)
    fatal(errno, "gettimeofday");
  struct timespec ts;
  ts.tv_sec = tv.tv_sec;
  ts.tv_nsec = tv.tv_usec * 1000;
  return ts;
#endif
}
