/* arena.h - arena buffer allocation header */

#ifndef __arenah
#define __arenah

typedef struct _ARENA_BLK {
	struct _ARENA_BLK * next;
	size_t size;
} ARENA_BLK;

typedef struct _ARENA {
	size_t avail;
	char * p;
	ARENA_BLK * curblk;
	ARENA_BLK * used;
	size_t blksize;
	size_t maxsize;
	ARENA_BLK ** backing;
} ARENA;

/* function prototypes */

extern void arenaInit (ARENA * a, size_t blksize, size_t maxsize,
		       ARENA_BLK ** backing);
extern void * arenaAlloc (ARENA * a, size_t n);
extern void arenaFree (ARENA * a);


#endif /* __arenah */
