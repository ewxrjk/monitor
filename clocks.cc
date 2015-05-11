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
#include <ctime>
#include <sys/time.h>
#if __APPLE__
#include <mach/mach_time.h>
#endif

#if HAVE_CLOCK_GETTIME
static double time_posix(clockid_t c) {
  struct timespec ts;
  if(clock_gettime(c, &ts) < 0)
    fatal(errno, "clock_gettime %#x", (unsigned)c);
  return ts.tv_sec + ts.tv_nsec / 1.0E9;
}
#endif

double time_monotonic() {
#if HAVE_CLOCK_GETTIME
  return time_posix(CLOCK_MONOTONIC);
#elif __APPLE__
  static struct mach_timebase_info mtbi;
  static bool mtbi_set;
  if(!mtbi_set) {
    kern_return_t rc = mach_timebase_info(&mtbi);
    if(rc)
      fatal(0, "mach_timebase_info: error %d", rc);
  }
  uint64_t t = mach_absolute_time();
  return (double)t * mtbi.numer / (1.0E9 * mtbi.denom);
#else
#error port me
#endif
}

double time_realtime() {
#if HAVE_CLOCK_GETTIME
  return time_posix(CLOCK_REALTIME);
#else
  struct timeval tv;
  if(gettimeofday(&tv, NULL) < 0)
    fatal(errno, "gettimeofday");
  return tv.tv_sec + tv.tv_usec / 1.0E6;
#endif
}
