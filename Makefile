GCC5_INSTALLED = $(shell gcc-5 --version 2>/dev/null)

ifeq ($(GCC5_INSTALLED),)
	CC = cc
else
	CC = gcc-5
endif

CFLAGS = -DDEBUG -std=c11 -flto -Wextra -Wall -Wno-unused -g
LDFLAGS = -ltickit -lpthread

all: irc

.PHONY: irc
irc: irc.c
	$(CC) $(CFLAGS) -o irc irc.c $(LDFLAGS)
