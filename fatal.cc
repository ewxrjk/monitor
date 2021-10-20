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
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unistd.h>

/* Called to clean up before reporting an fatal error */
int (*onfatal)(void);

/* Set inside a fork */
bool forking;

/* Report an error and terminate */
void fatal(int errno_value, const char *fmt, ...) {
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
  if(forking)
    _exit(1);
  else
    exit(1);
}
