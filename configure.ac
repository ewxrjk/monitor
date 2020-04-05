# This file is part of monitor.
# Copyright (C) 2015 Richard Kettlewell
# 
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
# 
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
# USA
AC_PREREQ([2.61])
AC_INIT([monitor], [0.2], [rjk@greenend.org.uk])
AC_CONFIG_AUX_DIR([config.aux])
AM_INIT_AUTOMAKE([foreign])
m4_ifdef([AM_SILENT_RULES], [AM_SILENT_RULES([yes])])
AC_CONFIG_SRCDIR([monitor.cc])
AM_CONFIG_HEADER([config.h])
AC_LANG([C++])
AC_PROG_CXX
AC_SET_MAKE
AC_CHECK_LIB([rt],[clock_gettime])
AC_CHECK_FUNCS([clock_gettime])
AC_CHECK_FUNC([iconv_option],[],[AC_CHECK_LIB([iconv],[iconv_open])])
PKG_CHECK_MODULES([ncurses],[ncursesw],
  [],
  [PKG_CHECK_MODULES([ncurses],[ncurses],
    [],[AC_CHECK_LIB([curses],[setcchar],
         [AC_SUBST([ncurses_LIBS],[-lcurses])
          AC_SUBST([ncurses_CFLAGS],[])],
         [AC_CHECK_LIB([cursesw],[setcchar],
           [AC_SUBST([ncurses_LIBS],[-lcursesw])
            AC_SUBST([ncurses_CFLAGS],[])])])])])
AC_CHECK_LIB([m],[floor],[LIBM=-lm])
AC_SUBST([LIBM])
AC_DEFINE([_GNU_SOURCE], [1], [use GNU extensions])
if test "x$GXX" = xyes; then
  werror="-Werror"
  coverage="-fprofile-arcs -ftest-coverage"
  CXX="$CXX -Wall -W -Wpointer-arith -Wwrite-strings -Wmissing-declarations -Wshadow"
fi

AC_ARG_ENABLE([werror],[AS_HELP_STRING([--disable-werror],[don't use -Werror])],
              [],[enable_werror=yes])
if test "$enable_werror" = yes; then
  CXX="$CXX $werror"
fi

AC_ARG_ENABLE([coverage],[AS_HELP_STRING([--enable-coverage],
                                         [compile with coverage information])])
if test "$enable_coverage" = yes; then
  CX="${CXX} ${coverage}"
fi

AC_ARG_WITH([broken-iconv],
  [AS_HELP_STRING([--with-broken-iconv],[support broken iconv() prototype])],
  AC_DEFINE([HAVE_BROKEN_ICONV],[1],[define if iconv() prototype is broken]))

AH_BOTTOM([#ifdef __GNUC__
# define attribute(x) __attribute__(x)
#else
# define attribute(x)
#endif])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
