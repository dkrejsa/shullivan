/* arena.c - implement arena buffer allocation */

#include <stddef.h>
#include <stdlib.h>
#include <assert.h>

#include "arena.h"

/*
 * An arena allocator provides a simple, high-performance memory
 * allocator in which blocks allocated from an arena (using 
 * arenaAlloc()) are not freed individually, but are freed all at
 * once in an arenaFree() call.
 */

/*
 * Initialize an arena. <blksize> is the default block size; it
 * will grow (up to a limit <maxsize>) if allocations are done which are
 * bigger than the current blksize over 4 and memory is not immediately
 * available in the current block.
 * If <backing> is non-null, it points at the address of a the head
 * of a simple list of free blocks, to which memory blocks will be
 * returned when arenaFree() is called, and from which memory will be
 * taken (if available) before resorting to the systmem pool.
 */

void
arenaInit (ARENA * a, size_t blksize, size_t maxsize,
	   ARENA_BLK ** backing)
{
	assert (a != NULL && blksize >= 1024);

	a->avail = 0;
	a->p = NULL;
	a->curblk = NULL;
	a->used = NULL;
	a->blksize = blksize;
	a->maxsize = maxsize;
	a->backing = backing;
}

/*
 * Allocate a block of size <n> within the arena <a>.
 * The memory is not initialized.  Blocks may not be individually
 * released, but all blocks allocated in a given arena may be
 * released at once by calling arenaFree().
 *
 * Note, arenaAlloc(a, 0) may return NULL.
 */

#define ARENA_ALIGN	8

void *
arenaAlloc (ARENA * a, size_t n)
{
	void * buf;
	ARENA_BLK * blk;

	n = (n + (ARENA_ALIGN - 1)) & ~(ARENA_ALIGN - 1);

	if (a->avail >= n) {
		buf = a->p;
		a->p += n;
		a->avail -= n;
		return buf;
	}

	/* the current block is used up */

	if (a->curblk != NULL) {
		a->curblk->next = a->used;
		a->used = a->curblk;
		a->curblk = NULL;
		a->avail = 0;
	}

	while (n > a->blksize / 4) {
		if (a->blksize * 2 > a->maxsize)
			return NULL;
		a->blksize = a->blksize * 2;
	}

	if (a->backing != NULL) {
		while ((blk = *a->backing) != NULL) {
			*a->backing = blk->next;
			if (blk->size >= a->blksize)
				goto haveblk;
			free (blk);
		}
	}

	if ((blk = malloc (a->blksize)) == NULL)
		return NULL;

	blk->size = a->blksize;

haveblk:
	blk->next = NULL;
	a->curblk = blk;

	buf = (blk + 1);
	a->avail = blk->size - sizeof (*blk) - n;
	a->p = (char *)buf + n;
	return buf;
}

/* Release all memory blocks held in the arena <a> */
void
arenaFree (ARENA * a)
{
	ARENA_BLK * blk;
	ARENA_BLK * next;

	if (a->curblk != NULL) {
		a->curblk->next = a->used;
		a->used = a->curblk;
		a->curblk = NULL;
		a->avail = 0;
	}

	if ((blk = a->used) == NULL)
		return;

	if (a->backing != NULL) {
		while (blk->next != NULL)
			blk = blk->next;
		blk->next = *a->backing;
		*a->backing = a->used;
		a->used = NULL;
		return;
	}

	/* if there's no backing store, release to the system heap */

	do {
		next = blk->next;
		free (blk);
	} while ((blk = next) != NULL);

	a->used = NULL;
	return;
}
