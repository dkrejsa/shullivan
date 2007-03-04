/* map.c - implement mappings as splay trees */

#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <assert.h>

#include "map.h"

/*
 * Done with splay trees just for fun!
 * http://www.link.cs.cmu.edu/splay/
 * Based upon the version top-down-splay.c by D. Sleator
 * Modified to avoid redundant compares, which for strings
 * are more expensive than a simple integer compare.
 */

typedef struct _SPLAY_MAP_ELEM SPLAY_MAP_ELEM;

struct _SPLAY_MAP_ELEM {
	MAP_ELEM me;
	SPLAY_MAP_ELEM * left;
	SPLAY_MAP_ELEM * right;
};

typedef struct _SPLAY_MAPPING {
	MAPPING map;
	SPLAY_MAP_ELEM * head;
	CMP_FUNC compare;
} SPLAY_MAPPING;

#define MAP_ELEM_BUNCH	128

#define SPLAYV(domElem, t, pCompare, compare) \
	((compare) ? splay ((domElem), (t), (pCompare), (compare)) : \
	 splay0 ((domElem), (t), (pCompare)))

#define SPLAY(m, domElem, pCompare) \
	do { \
		if (m->compare) \
			m->head = splay (domElem, m->head, \
					 pCompare, m->compare); \
		else \
			m->head = splay0 (domElem, m->head, pCompare); \
	} while ((0))


static SPLAY_MAP_ELEM * splay (void * domElem, SPLAY_MAP_ELEM * t, 
			       int * pCompare, CMP_FUNC compare);

static SPLAY_MAP_ELEM * splay0 (void * domElem, SPLAY_MAP_ELEM * t, 
				int * pCompare);

static void * walk (SPLAY_MAP_ELEM * tree, ENUMERATE_FUNC f,
		    void * ctx);

static SPLAY_MAP_ELEM * freeElems = NULL;

unsigned long numMapElems = 0;
unsigned long freeMapElems = 0;
unsigned long mappings = 0;

MAPPING *
mappingCreate (CMP_FUNC compare)
{
	SPLAY_MAPPING * t;
	t = malloc (sizeof (*t));
	if (t == NULL) {
		return NULL;
	}
	++mappings;
	t->map.user = NULL;
	t->map.size = 0;
	t->head = NULL;
	t->compare = compare;
	t->map.defval.p = NULL;
	return &t->map;
}

void
mappingEmpty (MAPPING * table, MAP_DELETE_FUNC f, void * ctx)
{
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;
	SPLAY_MAP_ELEM * me;

	assert (t != NULL);

	while ((me = t->head) != NULL) {
		if (f)
			f (ctx, &me->me);
		mapElemDelete (me->me.obj, &t->map);
	}
}

void
mappingDelete (MAPPING * table, MAP_DELETE_FUNC f, void * ctx)
{
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;
	SPLAY_MAP_ELEM * me;

	assert (t != NULL);

	while ((me = t->head) != NULL) {
		if (f)
			f (ctx, &me->me);
		mapElemDelete (me->me.obj, &t->map);
	}
	free (t);
	--mappings;
}

MAP_ELEM *
mapElemFind (void * domElem, MAPPING * table)
{
	int cmp;
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;

	if (t->head == NULL)
		return NULL;

	SPLAY (t, domElem, &cmp);
	if (cmp == 0)
		return (MAP_ELEM *)t->head;

	return NULL;
}

void *
mapVal (void * domElem, MAPPING * table)
{
	int cmp;
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;

	if (t->head == NULL)
		return NULL;

	SPLAY (t, domElem, &cmp);
	if (cmp == 0)
		return t->head->me.v.p;

	return NULL;
}

long
mapValI (void * domElem, MAPPING * table)
{
	int cmp;
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;

	if (t->head != NULL) {

		SPLAY (t, domElem, &cmp);
		if (cmp == 0)
			return t->head->me.v.i;
	}

	return t->map.defval.i;
}

MAP_ELEM *
mapElemArb (MAPPING * table)
{
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;

	if (t->head == NULL)
		return NULL;

	return &t->head->me;
}


/* mapElemNext() does not splay */

MAP_ELEM *
mapElemNext (void * domElem, MAPPING * table)
{
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;
	SPLAY_MAP_ELEM * me;
	SPLAY_MAP_ELEM * possible;

	me = t->head;

	possible = NULL;

	if (t->compare) {
		for (;;) {
			if (me == NULL)
				return (MAP_ELEM *)possible;

			if (t->compare (domElem, me->me.obj) < 0) {
				possible = me;
				me = me->left;
				continue;
			}
			me = me->right;
		}
	} else {
		for (;;) {
			if (me == NULL)
				return (MAP_ELEM *)possible;

			if (domElem < me->me.obj) {
				possible = me;
				me = me->left;
				continue;
			}
			me = me->right;
		}
	}
	/* NOT REACHED */
}

/* mapElemFirst() does not splay */

MAP_ELEM *
mapElemFirst (MAPPING * table)
{
	SPLAY_MAPPING * t = (SPLAY_MAPPING *) table;
	SPLAY_MAP_ELEM * me;

	me = t->head;
	if (me == NULL)
		return NULL;

	while (me->left != NULL)
		me = me->left;

	return &me->me;
}

/* Insert <new> into the tree <t>, unless it's already there.    */
/* Return a pointer to the resulting tree.                 */

/*
 * Note, one can see whether the MAP_ELEM was already present
 * in the tree before insertion by checking if the returned
 * value is equal to the original <mapElem> parameter.
 */

extern MAP_ELEM *
mapElemInsert (void * domElem, MAPPING * table)
{
	SPLAY_MAP_ELEM * new;
	SPLAY_MAPPING * tbl = (SPLAY_MAPPING *)table;
	SPLAY_MAP_ELEM * t = tbl->head;
	int i;
	int cmp;

	if ((new = freeElems) == NULL) {
		new = malloc (MAP_ELEM_BUNCH * sizeof (*new));
		if (new == NULL)
			return NULL;
		numMapElems += MAP_ELEM_BUNCH;
		freeMapElems = MAP_ELEM_BUNCH;
		i = MAP_ELEM_BUNCH - 1;
		new[i].me.obj = NULL;
		while (i > 0) {
			new [i-1].me.obj = &new[i];
			i = i-1;
		}
		freeElems = new;
	}

	if (t == NULL) {
		new->left = new->right = NULL;
		goto insert;
	}

	t = SPLAYV (domElem, t, &cmp, tbl->compare);

	if (cmp < 0) {
		new->left = t->left;
		new->right = t;
		t->left = NULL;
	} else if (cmp > 0) {
		new->right = t->right;
		new->left = t;
		t->right = NULL;
	} else { /* We get here if it's already in the tree */
		/* Don't add it again                      */
		tbl->head = t;
		return (MAP_ELEM *)t;
	}

insert:

	freeElems = new->me.obj; /* next in list */
	--freeMapElems;

	new->me.obj = domElem;
	new->me.v = tbl->map.defval;

	tbl->map.size++;
	tbl->head = new;
	return (MAP_ELEM *)new;
}

/*
 * Returns 1 if an element was found and deleted from the mapping.
 * Returns 0 if <domElem> wasn't found in the mapping's domain.
 */

extern int
mapElemDelete (void * domElem, MAPPING * mapping)
{

	SPLAY_MAPPING * map = (SPLAY_MAPPING *) mapping;
	SPLAY_MAP_ELEM * t = map->head;
	SPLAY_MAP_ELEM * x;
	int cmp;

	if (t==NULL)
		return 0;

	t = SPLAYV (domElem, t, &cmp, map->compare);
	if (cmp == 0) {			/* found it */
		if (t->left == NULL) {
			x = t->right;
		} else {
			x = SPLAYV (domElem, t->left, &cmp, 
				    map->compare);
			x->right = t->right;
		}
		map->map.size--;
		map->head = x;
		t->me.obj = freeElems;
		freeElems = t;
		++freeMapElems;
		return 1;
	}
	map->head = t;
	return 0;			/* It wasn't there */
}

/*
 * Based upon the version top-down-splay.c by D. Sleator
 *
 * It splays the tree with top node <t> according to <name>,
 * which need not occur in the tree, and returns the new top
 * node.  The pFound argument is used to avoid another string
 * compare to check for an exact match. When the tree is not
 * empty, the <pCompare> argument returns the comparison of
 * the specified <name> with the new top node. This is used to
 * avoid requiring an extra string compare.
 */

/* Simple top down splay, not requiring i to be in the tree t.  */
/* What it does is described above.                             */

static SPLAY_MAP_ELEM *
splay (void * domElem, SPLAY_MAP_ELEM * t, int * pCompare, 
       CMP_FUNC compare)
{
	SPLAY_MAP_ELEM N;
	SPLAY_MAP_ELEM *l;
	SPLAY_MAP_ELEM *r;
	SPLAY_MAP_ELEM *y;
	int cmp;

	if (t == NULL)
		return t;
	N.left = N.right = NULL;
	l = r = &N;

	cmp = compare (domElem, t->me.obj);
	for (;;) {
		if (cmp < 0) {
			if (t->left == NULL)
				break;
			cmp = compare (domElem, t->left->me.obj);
			if (cmp < 0) {
				y = t->left;	/* rotate right */
				t->left = y->right;
				y->right = t;
				t = y;
				if (t->left == NULL)
					break;
				cmp = compare (domElem, 
					       t->left->me.obj);
			}
			r->left = t;		/* link right */
			r = t;
			t = t->left;
		} else if (cmp > 0) {
			if (t->right == NULL)
				break;
			cmp = compare (domElem,
				       t->right->me.obj);
			if (cmp > 0) {
				y = t->right;	/* rotate left */
				t->right = y->left;
				y->left = t;
				t = y;
				if (t->right == NULL)
					break;
				cmp = compare (domElem,
					       t->right->me.obj);
			}
			l->right = t;		/* link left */
			l = t;
			t = t->right;
		} else {
			break;
		}
	}
	l->right = t->left;			/* assemble */
	r->left = t->right;
	t->left = N.right;
	t->right = N.left;
	*pCompare = cmp;
	return t;
}

/*
 * Version of splay optimized for simple pointer comparison.
 */
static SPLAY_MAP_ELEM *
splay0 (void * domElem, SPLAY_MAP_ELEM * t, int * pCompare)
{
	SPLAY_MAP_ELEM N;
	SPLAY_MAP_ELEM *l;
	SPLAY_MAP_ELEM *r;
	SPLAY_MAP_ELEM *y;
	int cmp;

	if (t == NULL)
		return t;
	N.left = N.right = NULL;
	l = r = &N;

	for (;;) {
		if ((char *)domElem < (char *)t->me.obj) {
			cmp = -1;
			if (t->left == NULL)
				break;
			if ((char *)domElem < (char *)t->left->me.obj) {
				y = t->left;	/* rotate right */
				t->left = y->right;
				y->right = t;
				t = y;
				if (t->left == NULL)
					break;
			}
			r->left = t;		/* link right */
			r = t;
			t = t->left;
		} else if ((char *)domElem > (char *)t->me.obj) {
			cmp = 1;
			if (t->right == NULL)
				break;
			if ((char *)domElem > 
			    (char *)t->right->me.obj) {
				y = t->right;	/* rotate left */
				t->right = y->left;
				y->left = t;
				t = y;
				if (t->right == NULL)
					break;
			}
			l->right = t;		/* link left */
			l = t;
			t = t->right;
		} else {
			cmp = 0;
			break;
		}
	}
	l->right = t->left;			/* assemble */
	r->left = t->right;
	t->left = N.right;
	t->right = N.left;
	*pCompare = cmp;
	return t;
}

void *
mappingEnumerate (MAPPING * t, ENUMERATE_FUNC f, void * ctx)
{
	SPLAY_MAPPING * map = (SPLAY_MAPPING *) t;

	assert (map != NULL && f != NULL);

	return walk (map->head, f, ctx);
}

/* Walk the tree, without splaying on the way... */

static void *
walk (SPLAY_MAP_ELEM * tree, ENUMERATE_FUNC f, void * ctx)
{
	void * res;

	if (tree == NULL)
		return NULL;

	if ((res = walk (tree->left, f, ctx)) != NULL)
		return res;
	if ((res = f (ctx, &tree->me)) != NULL)
		return res;

	return walk (tree->right, f, ctx);
}


