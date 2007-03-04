/* shul_ident.h - header for shullivan identifier lookup tables */


#ifndef __INCshul_identh
#define __INCshul_identh

#include <stddef.h>
#include "map.h"

typedef struct _IDENT {
	int idlen;
	int refcount;
	char name [1]; /* Actually variable length, nul terminated */
} IDENT;

#define IDENT_LEN(stringlen) ((stringlen) + 1 + offsetof(IDENT, name))
#define NAME2ID(nadr) ((IDENT *)((char *)(nadr) - offsetof(IDENT,name)))

/*
 * An IDENT_TABLE is MAPPING in which each domain element is
 * an identifier name; the identifier itself is located with NAME2ID.
 * The type of the range element varies with the table usage.
 * strcmp() is used as the comparsion function.
 */
typedef MAPPING IDENT_TABLE;

extern unsigned long numIdents; /* Debug, number of IDENTs in use */

extern int shulIdentInit (void);
extern void identTableDelete (IDENT_TABLE * table);

extern IDENT * identAlloc (char * buf, int buflen);
extern int identFree (IDENT * id);
extern IDENT * identPrefixed (char * prefix, int pfxlen, IDENT * id);

#endif /* __INCshul_identh */
