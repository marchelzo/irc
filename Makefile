GCC5_INSTALLED = $(shell gcc-5 --version 2>/dev/null)

ifeq ($(GCC5_INSTALLED),)
	CC = cc
else
	CC = gcc-5
endif

CFLAGS = -DDEBUG -flto -std=c11 -Wextra -Wall -Wno-unused -O2

LDFLAGS = -lncurses
LDFLAGS += /usr/local/lib/libtermkey.a
LDFLAGS += /usr/local/lib/libtickit.a


all: irc

.PHONY: irc
irc: irc.c
	$(CC) -o irc irc.c $(CFLAGS) $(LDFLAGS)
