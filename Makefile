# Makefile for shullivan proof checker

CC		= gcc
CFLAGS		= -O2 -g -Wall
#CFLAGS		= -O0 -g -Wall
RELOC		= -c
RM		= rm -f
#LD		= ld
# Use the compiler for linking also
LD		= $(CC)
# LIBFLAGS	= -lreadline -ltermcap
LIBFLAGS	= -lreadline
LDFLAGS		= $(LIBFLAGS)

OBJS	= shullivan.o shul_ident.o map.o arena.o

all :	shul

shullivan.o : shullivan.c shullivan.h shul_ident.h map.h arena.h
	$(CC) $(CFLAGS) $(RELOC) -o $@ $<

shul_ident.o : shul_ident.c shul_ident.h map.h
	$(CC) $(CFLAGS) $(RELOC) -o $@ $<

map.o : map.c map.h
	$(CC) $(CFLAGS) $(RELOC) -o $@ $<

arena.o : arena.c arena.h
	$(CC) $(CFLAGS) $(RELOC) -o $@ $<

shul : $(OBJS)
	$(LD) $(LDFLAGS) -o $@ $(OBJS)

.PHONY : clean

clean :
	$(RM) shul $(OBJS)
