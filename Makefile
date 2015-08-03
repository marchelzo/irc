CC = gcc
CFLAGS = -DDEBUG -std=c11 -flto -Wall -g
LDFLAGS = -ltickit -lpthread

all: irc

.PHONY: irc
irc: irc.c
	$(CC) $(CFLAGS) -o irc irc.c $(LDFLAGS)
