/* map.h - interface for arbitrary map/set collection */

/*
 * An element of a mapping (ordered pair).  When 'val' is ignored, 
 * one may treat the mapping as a set (i.e., the domain).
 * If (o1, v1) and (o2, v2) are different elements of a mapping,
 * the domain elements o1 and o2 must compare as different with
 * the mapping's comparison function.
 *
 * Note that MAP_ELEM is just the visible public part of a larger
 * structure which contains implementation-specific members.
 */

typedef union _MAPVAL {
	void * p;
	long i;
} MAPVAL;

typedef struct _MAP_ELEM {
	void * obj;	/* The domain element. Lookups based on this. */
	MAPVAL v;	/* The corresponding range value. */
} MAP_ELEM;

/*
 * Domain element comparison function. Compares domain elements
 * e1 and e2; returns a negative, zero, or positive value when
 * e1 < e2, e1 == e2, or e1 > e2 in the required sense.  When
 * NULL is provided as the comparison function, e1 and e2 are
 * simply compared as addresses. Provide (CMP_FUNC)strcmp
 * as the comparsion function to compare domain elements as strings.
 */

typedef int (* CMP_FUNC) (void * e1, void * e2);

/*
 * MAPPING is just the visible public part of a larger
 * structure which contains implementation-specific members.
 */

typedef struct _MAPPING {
	void * user;		/* reserved for client use */
	unsigned int size;	/* number of elements; treat as read-
				   only */
	MAPVAL defval;		/* default range value for inserted
				   elements. mappingCreate() sets
				   defval.p = NULL */
} MAPPING;


/* Debug, number of map elements in use */
extern unsigned long numMapElems;
extern unsigned long freeMapElems;

extern MAPPING * mappingCreate (CMP_FUNC compare);

/*
 * mappingDelete() iterates through the elements of the specified
 * mapping in any convenient order, calling the deletion function
 * (if non-NULL) once for each mapping element before deleting that
 * element from the map.  When all elements have been deleted, the
 * mapping itself is freed.
 *
 * mappingEmpty() does everything mappingDelete() does, except that
 * it does not free the mapping itself after it has been emptied.
 */

typedef void (*MAP_DELETE_FUNC) (void * ctx, MAP_ELEM * me);
extern void mappingDelete (MAPPING * m, MAP_DELETE_FUNC f, void * ctx);

extern void mappingEmpty (MAPPING * m, MAP_DELETE_FUNC f, void * ctx);

/*
 * Look up the mapping element for the specified domain element.
 * Returns NULL if there is no such element in the domain.
 *
 * The range value may be changed at will in the returned MAP_ELEM;
 * the domain value should not be changed in any way which affects
 * its ordering with other domain values in the map. Similar 
 * restrictions apply to mapElemFirst(), mapElemNext(), and
 * mapElemInsert().
 */
extern MAP_ELEM * mapElemFind (void * domElem, MAPPING * m);

/*
 * If <domElem> belongs to the mapping's domain, returns the
 * corresponding range element. Otherwise, returns NULL. Note
 * that if (<domElem>, NULL) is an element of the mapping, this
 * routine will return NULL even though <domElem> belongs to the
 * domain.
 */
extern void * mapVal (void * domElem, MAPPING * m);

/*
 * Same as mapVal(), but returns the value as a long.
 * Returns m->defval.i if no matching element is found.
 */
extern long mapValI (void * domElem, MAPPING * m);

extern MAP_ELEM * mapElemFirst (MAPPING * m);
extern MAP_ELEM * mapElemNext (void * domElem, MAPPING * m);

/*
 * It's safe to delete the current MAP_ELEM while using this
 * macro to iterate over all elements of a mapping.
 */

#define MAP_ELEM_ITER_SAFE(m_, dElem_, dNxt_) \
	for (dElem_ = mapElemFirst(m_); \
	     dElem_ != NULL && \
	     (dNxt_ = mapElemNext(dElem_->obj, m_), 1); \
	     dElem_ = dNxt_)

/*
 * Retrieve an arbitrary element of the mapping <m>. Returns NULL
 * if the mapping is empty; otherwise, which element is returned
 * is implementation-specific. Typically the most quickly accessible
 * element (e.g. the tree root in a tree implementation) is returned.
 *
 * This routine is provided mostly as a quick way to perform an
 * operation on each map element when emptying the mapping, when
 * the order is not important, for example:
 *
 *   while (NULL != (me = mapElemArb (m))) {
 *           releaseItem (me->obj, me->v.p);
 *           mapElemDelete (me->obj, m);
 *   }
 *
 * Note that mapElemFirst() could also be used, but might not be
 * as efficient. mappingDelete() provides an alternative approach.
 */
extern MAP_ELEM * mapElemArb (MAPPING * m);


/*
 * Insert a default mapping element (<domElem>, defval) into the
 * map, if <domElem> does not already belong to the domain, and return
 * that new element (with the mapping's current default range value).
 * The range value may be immediately set in the returned mapping
 * element (if desired).
 *
 * If <domElem> alreadly belongs to the domain, returns the 
 * corresponding MAP_ELEM.
 */
extern MAP_ELEM * mapElemInsert (void * domElem, MAPPING * m);

/*
 * Returns 1 if <domElem> was found in the map's domain; in this
 * case the corresponding MAP_ELEM is removed and freed.
 *
 * Returns 0 if <domElem> was not found in the map's domain.
 */
extern int mapElemDelete (void * domElem, MAPPING * m);

/*
 * Enumeration function passed to mappingEnumerate().
 *
 * It is called for each element in the mapping.
 * If the enumeration function returns a non-NULL value, the
 * enumeration terminates and that value is returned by
 * mappingEnumerate().
 *
 * It is not safe to modify the mapping (other than possibly changing
 * range values) during execution of mappingEnumerate().  The
 * mapElemFirst() and mapElemNext() functions may be used to safely
 * walk through the mapping if it is necessary to modify the mapping
 * (e.g. delete elements) as one goes.
 */
typedef void * (*ENUMERATE_FUNC) (void * ctx, MAP_ELEM * me);

extern void * mappingEnumerate (MAPPING * m, 
				ENUMERATE_FUNC f, void * ctx);

