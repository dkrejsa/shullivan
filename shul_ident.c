/* shul_ident.c - implement identifier lookup tables */

#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <assert.h>

#include "shul_ident.h"

unsigned long numIdents = 0; /* Debug */

static IDENT_TABLE * allIdents = NULL;

/*
 * Strcmp() is defined here to avoid any dynamic linking overhead
 * from using strcmp() as a function pointer...
 */
int
Strcmp (void * s, void * t)
{
	unsigned char * s1 = s;
	unsigned char * t1 = t;
	int ch;

	while ((ch = *s1++) == *t1 && ch != '\0')
		++t1;
	return (ch - *t1);
}

int
shulIdentInit (void)
{
	if (allIdents != NULL)
		return -1;

	allIdents = mappingCreate (Strcmp);
	if (allIdents == NULL)
		return -1;

	return 0;
}

static void identEntryFree (void * ctx, MAP_ELEM * me)
{
	identFree (me->obj);
}

void
identTableDelete (IDENT_TABLE * table)
{
	mappingDelete (table, identEntryFree, NULL);
}

IDENT *
identAlloc (char * buf, int buflen)
{
	IDENT * id;
	MAP_ELEM * me;

	assert (buf != NULL && buflen > 0 &&
		buf[buflen] == '\0');

	me = mapElemInsert (buf, allIdents);
	if (me == NULL)
		return NULL;

	if (buf != (char *)me->obj) {
		id = NAME2ID (me->obj);
		id->refcount++;
		return id;
	}

	/*
	 * For now, very simple. Later we'll think about interning
	 * symbols.
	 */
	id = malloc (IDENT_LEN (buflen));
	if (id == NULL) {
		mapElemDelete (me->obj, allIdents);
		return NULL;
	}

	++numIdents;
	id->idlen = buflen;
	memcpy (id->name, buf, buflen + 1);
	id->refcount = 1;
	me->obj = id->name;

	return id;
}

int
identFree (IDENT * id)
{
	int count;
	assert (id != NULL && id->refcount > 0);
	if ((count = --id->refcount) == 0) {
		mapElemDelete (id->name, allIdents);
		free (id);
		--numIdents;
	}
	return count;
}

IDENT *
identPrefixed (char * prefix, int pfxlen, IDENT * id)
{
	IDENT * res;
	int idlen;
	MAP_ELEM * me;

	assert (id != NULL);

	/*
	 * We can now return id directly if there is no prefix
	 * since an IDENT may belong to more than one mapping.
	 */
	if (prefix == NULL) {
		id->refcount++;
		return id;
	}

	idlen = id->idlen + pfxlen;

	res = malloc (IDENT_LEN(idlen));
	if (res == NULL)
		return NULL;

	res->idlen = idlen;
	memcpy (res->name, prefix, pfxlen);
	memcpy (res->name + pfxlen, id->name, id->idlen + 1);

	me = mapElemInsert (res->name, allIdents);
	if (me == NULL) {
		free (res);
		return NULL;
	}

	if (res->name != (char *)me->obj) {
		free (res);
		res = NAME2ID (me->obj);
		res->refcount++;
		return res;
	}

	res->refcount = 1;
	++numIdents;
	return res;
}

