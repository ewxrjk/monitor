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
bin_PROGRAMS=monitor
monitor_SOURCES=monitor.cc clocks.cc fatal.cc monitor.h
monitor_CPPFLAGS=$(ncurses_CFLAGS) -D_XOPEN_SOURCE_EXTENDED
monitor_LDADD=$(ncurses_LIBS) $(LIBM)
man_MANS=monitor.1
EXTRA_DIST=debian/changelog debian/compat debian/control	\
debian/copyright debian/rules debian/source/format README.md	\
${man_MANS}
