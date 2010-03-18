/* shullivan.c - C implementation of Ghilbert theorem checker */

#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <assert.h>

#include "shullivan.h"

#define ALLOC_ERR() \
    fprintf (stderr, "Allocation error (%s, line %d)\n", __FILE__, __LINE__)

typedef struct _GROWBUF {
	void * buf;
	size_t size;
} GROWBUF;

#define COMMAND_ERR		-1
#define COMMAND_EOF		0
#define COMMAND_CONTINUE_GOOD	1
#define COMMAND_CONTINUE_BAD	2

typedef enum _SCAN_RESULT {
	SCAN_ERR = -1,
	SCAN_EOF = 0,
	SCAN_ID = 1,	/* identifier */
	SCAN_LPAREN = 2,
	SCAN_RPAREN = 3,
	/* values greater than 3 indicate keywords in a scanner-
	   specific fashion */
} SCAN_RESULT;

typedef enum _SCAN_FLAGS {
	SF_EOF = 1,	/* read_more has reached EOF */
	SF_WS = 2,	/* insert implicit white-space char before next
			   read_more () */
} SCAN_FLAGS;

/* 
 * Minimum buffer length for scanner identifier buffer.
 * This ensures there is space for all our keywords, etc.
 */

#define SCAN_ID_BUFLEN_MIN	1024

typedef struct _SCANNER SCANNER;

typedef int (*SCANNER_GET_TOKEN) (SCANNER * scan);
typedef char * (*SCANNER_READ_MORE) (SCANNER * scan, void * ctx);
typedef void (*SCANNER_FREE_LINE) (char * line, 
				   SCANNER * scan, void * ctx);
typedef int (*SCANNER_PROMPT_SET) (SCANNER * scan, char * prompt);

typedef void (*SCANNER_CLEANUP) (SCANNER * scan);

struct _SCANNER {
	char * curline;
	int len;
	int ix;
	uint32_t flags;
	SCANNER_GET_TOKEN get_token;
	SCANNER_READ_MORE read_more;
	SCANNER_FREE_LINE free_line;
	SCANNER_PROMPT_SET prompt_set;
	SCANNER_CLEANUP cleanup;
	void * ctx;
	GROWBUF gb;
	int idlen;  /* length of identifier in buf */
	unsigned int lineno;
};

typedef enum _HTYPE {
	HT_IMPORT,
	HT_EXPORT,
	HT_THM,
	HT_DEF,
	HT_VAROLDKIND,	/* Record a variable's old kind. Must be immediately
			   followed by HT_VARNEWKIND. */
	HT_VARNEWKIND,	/* Record a variable's old kind. Must be immediately
			   followed by HT_VAR. */
	HT_VAR,		/* Add a variable */
	HT_KINDBIND0,	/* records old kind for immeiately following 
			   kindbind */
	HT_KINDBIND	/* a .gh-style kindbind */
} HTYPE;

typedef struct _HISTORY_ITEM {
	HTYPE htype;
	void * it;
} HISTORY_ITEM;

/*
 * The shullivan history is a two-level array of HISTORY_ITEMs.
 * Each entry in the top level array is a pointer to  a 'chunk'
 * of 1024 history items.
 */

#define HISTORY_CHUNK_SIZE	1024
typedef struct _HISTORY_CHUNK {
	HISTORY_ITEM h [HISTORY_CHUNK_SIZE];
} HISTORY_CHUNK;

#define HISTORY_TOP_LEVEL_SIZE	16384

typedef struct _DVWORK {
	int i;
	IDENT * id;
} DVWORK;

typedef struct _SHULLIVAN {
	ITEM * freeItems;
	MAPPING * interfaces;		/* imports */
	MAPPING * syms;			/* theorems/statements,
					   variables */
	MAPPING * terms;		/* terms & defs */
	MAPPING * kinds;		/* kinds */

	MAPPING * varIndex;		/* Scratch variable index mapping
					   used by parseStatement() and
					   load_def() and export_stmt() */

	GROWBUF vi;			/* shared buffer for EXPR_VARINFO's
					   used by parseStatement() and
					   load_def() and export_stmt() */

	GROWBUF env;			/* scratch buffer for environment
					   info in proof steps. Used in 
					   proofStepApply() */

	int ndvvars;			/* number of vars pairs of which
					   will fit in dvbits */
	int dvsize;			/* size in bytes of dvbits buffer */
	uint32_t * dvbits;		/* scratch buffer for DV calcs in
					   proofStepApply() */

	GROWBUF dvw;			/* DV work buffer */

	MAPPING * fvi;			/* scratch free variable sets */
	MAPPING * fvj;			/* fvi, fvj used in proofStepApply() */

	ARENA_BLK * backing;

	char delim;			/* search path delimiter character, 
					   default ':' */
	char ** path;			/* array of directories for imports */
	int ndirs;			/* number of dirs in the search path */
	HISTORY_CHUNK ** history;
	unsigned long histlen;
	unsigned long histmax;		/* size of top level array */

	int saveProof;			/* if not 0, save proof info */

	int verbose;			/* verbosity level */
#define SHUL_VERB_PROGRESS	1	/* note import, export, thm verify */
#define SHUL_VERB_COMMANDS	2	/* echo all commands */
#define SHUL_VERB_PROOF		4	/* print all results in proof */
#define SHUL_VERB_PRFWILD	8	/* print wild var hyps in pf. */
#define SHUL_VERB_PRINT_PRETTY	16	/* pretty-print expressions */

	unsigned long flags;

#define MULTIPLE_CONCLUSIONS	1	/* Allow 0 or more conclusions */
#define LOOSE_VAR_KINDS		2	/* allow variable kind inferrence */
#define EXPORT_LOOSE_VAR_KINDS	4	/* var kind inference in export */
#define EXPORT_WARN_DV		8	/* Warn of unneeded DVs in export */
#define REQ_MULT_CONC_SYNTAX	16	/* Multiple conclusion syntax req'd. */
#define DEF_JUSTIFY		32	/* Require justification proof for
					   definitions with dummy variables. */
} SHULLIVAN;

typedef int (*COMMAND_FUNC) (SHULLIVAN * shul, ITEM * item);

typedef void * (*DV_ENUMERATE_FUNC) (int i, int j, void * ctx);

static void * dvEnumerate (int nvars, uint32_t * dvbits,
			   DV_ENUMERATE_FUNC f, void * ctx);
static void sexpr_print (FILE * f, ITEM * item);
static void exprPrint (FILE * f, EXPR * exp, unsigned long verbose, 
		       int indent);
static int port (SHULLIVAN * shul, ITEM * args, int importing);
static void ifaceFree (SHULLIVAN * shul, INTERFACE * iface);

static char * shulPrompt = "shul=> ";
static char * shulContinuePrompt = "> ";

/*
 * Increase the size of gb's buffer to at least n bytes.
 * If gb's buffer is already at least n bytes, the function returns
 * successfully without changing the buffer size. Otherwise, the buffer
 * is grown (keeping its current contents).
 *
 * To avoid too many calls to this routine, the buffer size is
 * doubled until it reaches at least n bytes, or hits a very
 * large ceiling size.
 *
 * Returns 0 if buffer is at least n bytes after the call.
 * Returns -1 if the buffer is less than n bytes after the call.
 * In either case, the old buffer contents (if any) are retained.
 */
static int
growBuf (GROWBUF * gb, size_t n)
{
	void * p;
	size_t m;

	assert (gb != NULL);

	m = gb->size;
	if (m >= n)
		return 0;

	if (m == 0)
		m = 256;

	while (m < n && m * 2 < (size_t)0x80000000)
		m = m * 2;

	if (m < n)
		return -1;

	p = realloc (gb->buf, m);
	if (p == NULL)
		return -1;

	gb->buf = p;
	gb->size = m;
	return 0;
}

static int
growBufInit (GROWBUF * gb, size_t n)
{
	assert (gb != NULL && n > 0);

	if (gb->buf != NULL)
		free (gb->buf);

	gb->size = 0;

	if ((gb->buf = malloc (n)) == NULL)
		return -1;

	gb->size = n;
	return 0;
}

static int
histAdd (SHULLIVAN * shul, HTYPE htype, void * it)
{
	unsigned long len = shul->histlen;
	unsigned long topi = len / HISTORY_CHUNK_SIZE;
	HISTORY_CHUNK * chunk;

	len = len % HISTORY_CHUNK_SIZE;

	if (topi >= shul->histmax) {
		HISTORY_CHUNK ** ppChunk;

		assert (topi == shul->histmax && len == 0);

		/* Add top-level space for a 1024*1024 more items */
		fprintf (stderr, "Growing top-level history from "
			 "%lu to %lu\n",
			 shul->histlen, shul->histlen + 1024);
		ppChunk = realloc (shul->history,
				   ((shul->histmax + 1024) * 
				    sizeof (*shul->history)));
		if (ppChunk == NULL) {
			perror ("histAdd:realloc");
			return -1;
		}
		memset (shul->history + shul->histmax, 0,
			1024 * sizeof (*shul->history));
		shul->history = ppChunk;
		shul->histmax += 1024;
	}

	chunk = shul->history[topi];
	if (chunk == NULL) {
		assert (len == 0);
		chunk = malloc (sizeof (*chunk));
		if (chunk == NULL) {
			perror ("histAdd:malloc");
			return -1;
		}
		shul->history[topi] = chunk;
	}

	chunk->h[len].htype = htype;
	chunk->h[len].it = it;
	shul->histlen++;

	return 0;
}

static void
exprStackInit (EXPR_STACK * s, ARENA * a)
{
	assert (s != NULL);
	s->count = 0;
	s->maxsize = 0;
	s->exprs = NULL;
	s->arena = a;
}

static int
exprStackPush (EXPR_STACK * s, EXPR * e)
{
	EXPR ** expr;
	EXPR ** nexpr;

	expr = s->exprs;
	if (s->count >= s->maxsize) {
		assert (s->count == s->maxsize);

		if (s->maxsize == 0)
			s->maxsize = 32;
		else
			s->maxsize *= 2;

		nexpr = arenaAlloc (s->arena, 
				    s->maxsize * sizeof (EXPR *));
		if (nexpr == NULL) {
			ALLOC_ERR ();
			return -1;
		}
		memcpy (nexpr, expr, s->count * sizeof (EXPR *));
		s->exprs = nexpr;
		expr = nexpr;
	}
	expr[s->count++] = e;
	return 0;
}

static EXPR *
specialize (EXPR * e, EXPR ** env, ARENA * arena)
{
	int i;
	S_EXPR * sexpr;
	int arity;

	/*
	 * e is a conclusion of the statment being applied, not
	 * of the theorem being proven. As such, all its variables
	 * are of the ET_IVAR type. All the corresponding expressions in
	 * the environment are allocated in tip->arena, so we can
	 * simply return the pointer.
	 */

	if (e->ex.etype == ET_IVAR)
		return env[e->vi.index];

	assert (e->ex.etype == ET_SEXPR);

	arity = e->sx.t->arity;

	sexpr = arenaAlloc (arena,
			    offsetof (S_EXPR, args) + arity * sizeof (EXPR *));
	if (sexpr == NULL) {
		ALLOC_ERR ();
		return NULL;
	}

	sexpr->ex.etype = ET_SEXPR;
	sexpr->ex.kind = e->ex.kind;
	sexpr->t = e->sx.t;

	for (i = 0; i < arity; ++i) {
		if ((sexpr->args[i] = specialize (e->sx.args[i], env, arena))
		    == NULL)
			return NULL;
	}
	return (EXPR *)sexpr;
}

static int
match (EXPR * e1, EXPR * e2, EXPR ** env)
{
	int i;
	/* 
	 * e1 is the actual expression provided on the proof stack
	 * while e2 is the expression of the statement's formal hypothesis.
	 * When env is NULL, we are checking an exact match for a formal
	 * variable matched earlier.
	 */

#if 0
	printf ("match: ");
	exprPrint (stdout, e1, 0, 0);
	printf (" vs. ");
	exprPrint (stdout, e2, 0, 0);
	printf (" env %s\n", env ? "non-NULL" : "NULL");
#endif

	if (e2->ex.etype == ET_SEXPR) {
		if (e1->ex.etype != ET_SEXPR) {
			fprintf (stderr,
				 "Term mismatch. Wanted '(%s ...)', got "
				 "non-term.\n",
				 e2->sx.t->sym.ident->name);
			return -1;
		}
		if (e1->sx.t != e2->sx.t) {
			fprintf (stderr,
				 "Term mismatch. Wanted '(%s ...)', got "
				 "(%s ...)\n",
				 e2->sx.t->sym.ident->name,
				 e1->sx.t->sym.ident->name);
			return -1;
		}
		/* 
		 * It has already been checked that the number of arguments
		 * matches the arity for sexpr1 (when sexpr1 was being
		 * constructed).
		 */
		for (i = 0; i < e2->sx.t->arity; ++i) {
			if (match (e1->sx.args[i], e2->sx.args[i], env) != 0)
				return -1;
		}
		return 0;
	}

	/* All variables encountered have been converted to ET_IVARs */

	assert (e2->ex.etype == ET_IVAR);

	if (env == NULL) {
		char * name1;
		char * name2;

		/* We are performing an exact match involving
		 * variables of the statement being proved (ET_IVAR), or in
		 * the global symbol table (ET_VAR).
		 */

		if (e2 == e1)
			return 0;
		
		name2 = e2->vi.id->name;

		if (e1->ex.etype == ET_SEXPR) {
			fprintf (stderr, "Expected variable '%s', got "
				 "term (required exact match).\n", name2);
			return -1;
		}

		assert (e1->ex.etype == ET_IVAR);

		name1 = e1->vi.id->name;

		fprintf (stderr, "*** Expected variable '%s', got "
			 "variable '%s' (required exact match).\n",
			 name2, name1);
		
		return -1;
	}

	if (e1->ex.kind->rep != e2->ex.kind->rep) {
		fprintf (stderr,
			 "Kind mismatch (wanted %s, got %s)\n",
			 e2->ex.kind->id->name,
			 e1->ex.kind->id->name);
		return -1;
	}

	if (env[e2->vi.index] == NULL) {
#if 0
		printf ("map %s (%d) to ", e2->vi.id->name, e2->vi.index);
		exprPrint (stdout, e1, 0, 0);
		printf ("\n");
#endif
		env[e2->vi.index] = e1;
		return 0;
	}

	/* This ivar already assigned, check for exact match */
	return match (e1, env[e2->vi.index], NULL);
}

typedef struct _DVC {
	uint32_t * dvbits;  /* DV bitmap for theorem being proved */
	EXPR ** env;
	MAPPING * fvi;
	MAPPING * fvj;
} DVC;

typedef struct _VMAP {
	EXPR_VARINFO * vi;
	EXPR * ex;
} VMAP;

typedef struct _DVC2 {
	uint32_t * dvbits;  /* DV bitmap for theorem being proved */
	int missing;
	int bad;
	int nvars;	/* stat->nhvars + stat->nWild for theorem in prog. */
	int nhvars;	/* stat->nhvars */
	EXPR_VARINFO * vi;
	VMAP * vmap;
} DVC2;

static int
findVars (EXPR * e, MAPPING * m)
{
	MAP_ELEM * me;
	int i;

	if (e->ex.etype != ET_SEXPR) {
		assert (e->ex.etype == ET_IVAR);

		me = mapElemInsert (e, m);
		if (me == NULL) {
			ALLOC_ERR ();
			return -1;
		}
		/* Don't care about me->v, we're just using this as a set */
		return 0;
	}

	for (i = 0; i < e->sx.t->arity; ++i) {
		if (findVars (e->sx.args[i], m) != 0)
			return -1;
	}
	return 0;
}

static int
findVar (EXPR_VARINFO * vi, EXPR * e)
{
	int i;

	if (e->ex.etype != ET_SEXPR) {
		if (vi == &e->vi)
			return 1;
		return 0;
	}

	for (i = 0; i < e->sx.t->arity; ++i) {
		if (findVar (vi, e->sx.args[i]) != 0)
			return 1;
	}
	return 0;
}

static void *
getDvsForStat (int i, int j, void * ctx)
{
	DVC * dv = ctx;
	MAPPING * fvi = dv->fvi;
	MAPPING * fvj = dv->fvj;
	EXPR * ei;
	EXPR * ej;
	MAP_ELEM * mei;
	MAP_ELEM * meinext;
	MAP_ELEM * mej;
	MAP_ELEM * mejnext;
	uint32_t * bmap = dv->dvbits;
	void * ret;

	assert (fvi->size == 0 && fvj->size == 0);

	/*
	 * Hmm, it's somewhat inefficient to find the variables on each
	 * iteration this way, since we may have to find variables for the
	 * same expression (env entry)  more than once.
	 */
	findVars (dv->env[i], fvi);
	findVars (dv->env[j], fvj);

	MAP_ELEM_ITER_SAFE (fvi, mei, meinext) {
		MAP_ELEM_ITER_SAFE (fvj, mej, mejnext) {
			ei = mei->obj;
			ej = mej->obj;

			if (ei == ej) {
				fprintf (stderr,
					 "*** disjoint violation for '%s'\n",
					 ei->vi.id->name);
				ret = ei; /* arbitrary non-NULL */
				goto mapEmpty;
			}

			i = ei->vi.index;
			j = ej->vi.index;

			assert (i != j); /* since ei != ej */

			if (j < i) {
				int k = i;
				i = j;
				j = k;
			}

			/* Here we just accumulate all DV conditions
			   involving variables occuring in the theorem
			   hypotheses, conclusions, or anywhere in the proof.
			   We'll do the checking that the theorem specifies
			   the needed subset of these pairs */

			BIT_SET (bmap, PAIRNUM(i,j));
		}
	}

	ret = NULL;

mapEmpty:
	mappingEmpty (fvi, NULL, NULL);
	mappingEmpty (fvj, NULL, NULL);
	return ret;
}

static void *
checkDvsForStat (int i, int j, void * ctx)
{
	DVC2 * dv = ctx;
	EXPR * ex;
	EXPR_VARINFO * vi;
	EXPR_VARINFO * vj;


	/* Note, we are guaranteed that i < j */

	if (j < dv->nvars) {
		/*
		 * Both variables occur in the hypotheses or conclusions
		 * of the theorem being proved, so the theorem's DV
		 * set must contain the pair.
		 *
		 * Actually, if one of the variables occurs in the conclusions
		 * but not the hypotheses and also doesn't occur in the
		 * remnant, then the variable occurs on the LHS but not the
		 * RHS of a def occurring in the conclusion and is discarded
		 * in the def expansion.  In this case, the pair need not be
		 * included.
		 */

		if (BIT (dv->dvbits, PAIRNUM (i, j)) != 0)
			return NULL; /* Good, continue */

		if (j >= dv->nhvars &&
		    dv->vmap[j - dv->nhvars].ex == NULL)
			return NULL; /* j did not occur in remnant */

		if (i >= dv->nhvars &&
		    dv->vmap[i - dv->nhvars].ex == NULL)
			return NULL; /* i did not occur in remnant */

		if (!dv->missing) {
			fprintf (stderr, "Missing DV pairs (");
			dv->missing = 1;
		}

		fprintf (stderr, "(%s %s)",
			 dv->vi[i].id->name,
			 dv->vi[j].id->name);

		dv->bad = 1;
		return NULL; /* not OK, but continue to look for more */
	}

	/* 
	 * OK, at least one of the variables occurred in the proof
	 * steps but not in the hypotheses or conclusions.
	 * If one of the variables occurred in the remnant and was
	 * bound to a def dummy, and the other variable was
	 * not present in the corresponding sub-expression matched
	 * against the def expansion causing the binding of the first
	 * variable, consider this a failure.
	 *
	 * Note, it seems semi-reasonable to me that the variable bound to
	 * the def dummy shouldn't have DV restrictions with other variables.
	 *
	 * The way I look at it, in order to prove a conclusion involving
	 * def terms, one would have to show that one could prove the
	 * same conclusion with all the def terms expanded, with arbitrary
	 * independent substitutions for the def dummies. (This is a bit
	 * stronger than what Ghilbert requires.  For example, Ghilbert allows
	 * me to prove (-> (d1) (d1)) as a special case of id even where
	 * (d1) is a def term of kind wff which may contain dummies, and
	 * where expanding the two (d1)'s with different choices for the
	 * dummies would not be a valid result.)
	 *
	 * I'm not sure why it's not a violation if the 'other variable' was
	 * part of the sub-expression matched against the def expansion.
	 * There may be some assumption that the dummy variables in a def
	 * is always chosen distinct from the variables occurring in the
	 * actual def term arguments and the other dummy variables.
	 */

	vj = dv->vmap[j - dv->nhvars].vi;
	ex = dv->vmap[j - dv->nhvars].ex;

	/* If ex is NULL, variable j doesn't occur in the remnant or the
	 * hypotheses (or the conclusions either).
	 */
	if (ex == NULL)
		return NULL;

	/* At this point we know that variable j occurs in the remnant */

	if (i >= dv->nhvars && dv->vmap[i - dv->nhvars].ex == NULL)
		return NULL;	/* variable i doesn't occur in remnant
				   or the hypotheses */

	/*
	 * Note, for dv->nhvars <= k, variable k occurred in the remnant
	 * iff dv->vmap[k - dv->nhvars].ex != NULL.  But if
	 * dv->vmap[k - dv->nhvars].ex == (EXPR *)dv->vmap, then k
	 * occurs in the remnant but is not bound to a definition dummy.
	 */

	if (ex != (EXPR *)dv->vmap) {
		if (i < dv->nvars)
			vi = &dv->vi[i];
		else
			vi = dv->vmap[i - dv->nhvars].vi;

		if (findVar (vi, ex) == 0) {
			if (dv->missing) {
				fprintf (stderr, ")\n");
				dv->missing = 0;
			}
			fprintf (stderr,
				 "*** def dummy %s not distinct from %s\n",
				 vj->id->name,
				 vi->id->name);
			
			dv->bad = 1;
		}
	}

	/* 
	 * If i < dv->nvars, it can't have been bound to a definition
	 * dummy; that's checked by checkConclusion().
	 */

	if (i < dv->nvars)
		return NULL;

	ex = dv->vmap[i - dv->nhvars].ex;
	if (ex == (EXPR *)dv->vmap)
		return NULL;	/* i is in remnant, but not bound to def
				   dummy */

	if (findVar (vj, ex) == 0) {
		if (dv->missing) {
			fprintf (stderr, ")\n");
			dv->missing = 0;
		}
		vi = dv->vmap[i - dv->nhvars].vi;
		fprintf (stderr,
			 "*** def dummy %s not distinct from %s\n",
			 vi->id->name,
			 vj->id->name);
			
		dv->bad = 1;
	}
	return NULL;
}

static int
proofStepApply (SHULLIVAN * shul, TIP * tip, PROOF_STEP * s)
{
	STATEMENT * stat;
	EXPR * e1;
	EXPR * e2;
	EXPR ** env;
	DVC dv;
	int i;
	int j;
	int nvars;
	int indent;

	if (s->s.type == STEPT_HYP) {
		if (tip->wvs.count != 0) {
			fprintf (stderr,
				 "*** Hypothesis pushed with non-empty "
				 "wild variable stack.\n");
			return -1;
		}

		i = s->hyp.index;
		e1 = tip->t->stmt->hyps[i];
		if (shul->verbose & SHUL_VERB_PROOF) {
			j = printf ("H%d %s ", i+1, tip->t->hypnam[i]->name);
			exprPrint (stdout, e1, shul->verbose, j);
			printf ("\n");
		}
		return exprStackPush (&tip->ps, e1);
	}

	if (s->s.type == STEPT_EXPR) {
		/*
		 * We allow pushing any expression onto the wild
		 * variable hypothesis stack. All checking is done when
		 * a theorem reference is applied. If there is stuff
		 * left on the wvs stack at the end of the proof, a
		 * warning is generated.
		 */
		if (shul->verbose & SHUL_VERB_PRFWILD) {
			j = printf ("W  ");
			exprPrint (stdout, s->expr.x, shul->verbose, j);
			printf ("\n");
		}
		return exprStackPush (&tip->wvs, s->expr.x);
	}

	assert (s->s.type == STEPT_REF);

	stat = s->ref.stat;

	if (stat->nHyps > tip->ps.count) {
		fprintf (stderr,
			 "*** Proof stack underflow, needed %d items\n",
			 stat->nHyps);
		return -1;
	}

	/* 
	 * We don't allow saving items on the wild
	 * variable stack between references, so the counts
	 * must match exactly.
	 */
	if (stat->nWild != tip->wvs.count) {
		fprintf (stderr,
			 "*** Expected %d wild var hypotheses, "
			 "had %d\n", stat->nWild, tip->wvs.count);
		return -1;
	}

	/* 
	 * env holds information about the values assigned
	 * to variables occurring in the formal hypotheses
	 * and wild variables of the statement being
	 * referenced during the matching with the provided
	 * actual hypotheses.
	 */

	nvars = stat->nhvars + stat->nWild;

	if (nvars * sizeof (EXPR *) > shul->env.size &&
	    growBufInit (&shul->env, 2 * nvars * sizeof (EXPR *)) != 0) {
		perror ("proofStepApply:growBuf");
		return -1;
	}

	env = shul->env.buf;

	for (i = 0; i < nvars; ++i)
		env[i] = NULL;

	/* check explicit hypotheses */

	j = tip->ps.count - stat->nHyps;
	for (i = 0; i < stat->nHyps; ++i, ++j) {
		e1 = tip->ps.exprs[j];
		e2 = stat->hyps[i];
		if (match (e1, e2, env) != 0) {
			fprintf (stderr, "*** Hypothesis mismatch.\n");
			return -1;
		}
	}

	j = stat->nhvars;

	/* Assign wild hypothesis variables */

	for (i = 0; i < stat->nWild ; ++i) {
		assert (env[i+j] == NULL);

		if (stat->vi[i+j].ex.kind->rep != 
		    tip->wvs.exprs[i]->ex.kind->rep) {
			fprintf (stderr,
				 "Kind mismatch got %s wanted %s for %s\n",
				  tip->wvs.exprs[i]->ex.kind->id->name,
				  stat->vi[i+j].ex.kind->id->name,
				  stat->vi[i+j].id->name);

			return -1;
		}
		env[i+j] = tip->wvs.exprs[i];
#if 0
		printf ("mv map %s (%d) to ", stat->vi[i+j].id->name, i+j);
		exprPrint (stdout, tip->wvs.exprs[i], 0, 0);
		printf ("\n");
#endif
	}

	/* check distinct variable conditions */

	if (tip->varIndex->size > shul->ndvvars) {
		int n = tip->varIndex->size + 8;
		int pairs = n * (n - 1) / 2; /* sum (i=1..(n-1) | i) */
		int newsize = BIT_MAP_SIZE (pairs);
		uint32_t * dvbits;

		dvbits = calloc (1, newsize);
		if (dvbits == NULL) {
			perror ("proofStepApply:calloc");
			return -1;
		}

		assert (newsize > shul->dvsize);

		memcpy (dvbits, shul->dvbits, shul->dvsize);
		memset ((char *)dvbits + shul->dvsize, 0, 
			newsize - shul->dvsize);
		shul->ndvvars = n;
		shul->dvsize = newsize;
		free (shul->dvbits);
		shul->dvbits = dvbits;
	}

	dv.dvbits = shul->dvbits;
	dv.env = env;
	dv.fvi = shul->fvi;
	dv.fvj = shul->fvj;

	if (dvEnumerate (nvars, stat->dvbits,
			 getDvsForStat, &dv) != NULL) {
		return -1;
	}

	/* Clear the wild variable stack */

	tip->wvs.count = 0;

	/*
	 * OK, everything's good. Pop off the actual hypotheses
	 * and add the specialized conclusions:
	 */

	tip->ps.count -= stat->nHyps;

	indent = 0;
	if (shul->verbose & SHUL_VERB_PROOF) {
		if (stat->nCons == 0)
			printf ("-%d %s\n", stat->nHyps, 
				stat->sym.ident->name);
		else
			indent = printf ("-%d %s ", stat->nHyps,
					 stat->sym.ident->name);
	}

	for (i = 0; i < stat->nCons; ++i, ++j) {
		e1 = specialize (stat->cons[i], env, &tip->arena);
		if (e1 == NULL)
			return -1;
		if (shul->verbose & SHUL_VERB_PROOF) {
			if (i != 0)
				indent = printf ("+  ");
			exprPrint (stdout, e1, shul->verbose, indent);
			printf ("\n");
		}
		if (exprStackPush (&tip->ps, e1) != 0)
			return -1;
	}

	return 0;
}

static void
scannerInit (SCANNER * scan, 
	     SCANNER_READ_MORE readMore,
	     void * readMoreCtx,
	     SCANNER_FREE_LINE freeLine,
	     SCANNER_GET_TOKEN getToken,
	     SCANNER_PROMPT_SET promptSet,
	     SCANNER_CLEANUP cleanup)
{
	memset (scan, 0, sizeof (*scan));
	scan->get_token = getToken;
	scan->read_more = readMore;
	scan->ctx = readMoreCtx;
	scan->free_line = freeLine;
	scan->prompt_set = promptSet;
	scan->cleanup = cleanup;
	scan->gb.buf = NULL;
	scan->gb.size = 0;
}

#define SIMPLE_SCAN_LINE_LEN	4096

static char *
simpleScan (SCANNER * scan, void * ctx)
{
	char * line;
	char * prompt = (char *)ctx;

	line = malloc (SIMPLE_SCAN_LINE_LEN);
	if (line == NULL) {
		perror ("simpleScan:malloc");
		return NULL;
	}

	if (prompt) {
		fprintf (stdout, "%s", prompt);
		fflush (stdout);
	}

	if (fgets (line, SIMPLE_SCAN_LINE_LEN, stdin) == NULL)
		return NULL;

	return line;
}

static char *
readlineScan (SCANNER * scan, void * ctx)
{
	char * line;
	char * prompt = (char *)ctx;

	line = readline (prompt);
	if (line != NULL) {
		scan->flags |= SF_WS;
		if (*line != '\0')
			add_history (line);
	}
	return line;
}

static void
freeLine (char * line, SCANNER * scan, void * ctx)
{
	free (line); /* corresponding to readlineScan */
}

static int
scanToken (SCANNER * scan)
{
	int comment = 0;
	char * pch;
	char ch;

	if (scan->gb.buf == NULL &&
	    growBufInit (&scan->gb, SCAN_ID_BUFLEN_MIN)) {
		perror ("scanToken:malloc");
		return SCAN_ERR;
	}

	assert (scan->gb.size >= SCAN_ID_BUFLEN_MIN);

	scan->idlen = 0;

	pch = scan->gb.buf;

	for (;;) {
		if (scan->ix >= scan->len) {
			if ((scan->flags & SF_WS) != 0) {
				if (scan->lineno != 0)
					++scan->lineno;
				if (scan->idlen > 0)
					goto haveId;
			}
			if (scan->flags & SF_EOF) {
				if (scan->idlen > 0)
					goto haveId;
				return SCAN_EOF;
			}
			if (scan->curline)
				scan->free_line (scan->curline,
						 scan, scan->ctx);
			scan->ix = 0;
			scan->curline = scan->read_more (scan, 
							 scan->ctx);
			if (scan->curline == NULL) {
				scan->len = 0;
				scan->flags |= SF_EOF;
				return SCAN_EOF;
			}
			scan->len = strlen (scan->curline);
			if (comment)
				goto continue_comment;

			continue;
		}
		ch = scan->curline [scan->ix++];
		if (ch == '\n' && scan->lineno)
			++scan->lineno;
		if (isspace (ch)) {
			if (scan->idlen > 0)
				goto haveId;

			continue;
		}
		if (ch == '#') { /* Comment to end of line */
			int ix;

			comment = 1;

			/* Handle embedded newlines */
continue_comment:
			ix = scan->ix;
			while (ix < scan->len && 
			       scan->curline[ix] != '\n')
				++ix;
			if (ix < scan->len) { /* found '\n', pass it */
				++ix;
				comment = 0;
			} else if (scan->flags & SF_WS) {
				comment = 0;
			}
			scan->ix = ix;

			if (comment == 0 && scan->lineno)
				++scan->lineno;
			if (scan->idlen > 0)
				goto haveId;

			continue;
		}
		/* 
		 * Note, Ghilbert presently doesn't have any syntax for
		 * escaping whitespace or comment characters, or other
		 * special characters, in case these need to occur in
		 * a token (e.g. a path name).
		 * (Since the '$' character doesn't presently occur
		 * in set_mm.gh, it's a possible candidate for an
		 * escape character.  However, zfc-pax.gh uses '$'
		 * extensively, I guess we can't win. Punting for now.)
		 */

		if (ch == '(' || ch == ')') {
			if (scan->idlen > 0) {
				--scan->ix; /* put it back */
				goto haveId;
			}
			/* We're guaranteed enough space to store
			   at least SCAN_ID_BUFLEN_MIN char's */
			*pch++ = ch;
			*pch = '\0';
			scan->idlen = 1;

			if (ch == '(')
				return SCAN_LPAREN;
			return SCAN_RPAREN;
		}

		/* regular identifier or keyword */

		++scan->idlen;
		if (scan->idlen >= scan->gb.size &&
		    growBuf (&scan->gb, scan->idlen) != 0) {
			scan->idlen = 0;
			*(char *)scan->gb.buf = '\0';
			perror ("scanToken:growBuf");
			return SCAN_ERR;
		}
		*pch++ = ch;
	}

haveId:
	/*
	 * The code adding adding identifier characters above
	 * ensures that there is always enough space for the
	 * terminating NUL character in the buffer.
	 */

	*pch = '\0';
	return SCAN_ID;
}


#define NUM_ITEMS_BATCH		128

static ITEM *
itemAlloc (SHULLIVAN * shul)
{
	ITEM * item;
	int i;
	item = shul->freeItems;
	if (item == NULL) {

		item = malloc (NUM_ITEMS_BATCH * sizeof (*item));
		if (item == NULL)
			return NULL;

		item = item + NUM_ITEMS_BATCH - 1;
		item->it.next = NULL;

		for (i = NUM_ITEMS_BATCH - 1; i > 0; --i) {
			(item - 1)->it.next = item;
			item = item - 1;
		}
	}
	shul->freeItems = item->it.next;
	item->it.itype = -1;
	item->it.next = NULL;
	return item;
}

static void
itemFree (SHULLIVAN * shul, ITEM * item)
{
	item->it.next = shul->freeItems;
	shul->freeItems = item;
}


static ITEM *
read_sexpr (SHULLIVAN * shul, SCANNER * scan)
{
	int res;
	ITEM * item;
	ITEM ** ppItem;

	item = itemAlloc (shul);
	if (item == NULL)
		return NULL;

	res = scan->get_token (scan);

	if (res <= SCAN_EOF) {
		fprintf (stderr,
			 "EOF or error while reading s-expression\n");
		goto read_sexpr_bad;
	}

	if (res == SCAN_RPAREN) {
		/* Hmm, what if we find ')' at the top level? */
		goto read_sexpr_bad;
	}

	if (res == SCAN_LPAREN) {
		item->it.itype = IT_SLIST;
		ppItem = &item->sl.first;
		while ((*ppItem = read_sexpr (shul, scan)) != NULL)
			ppItem = &(*ppItem)->it.next;

		return item;
	}

	/* an identifier */

	assert (res == SCAN_ID);

	item->it.itype = IT_IDENT;

	if ((item->id.id = identAlloc (scan->gb.buf, scan->idlen)) != NULL)
		return item;

read_sexpr_bad:
	itemFree (shul, item);
	return NULL;
}

static void
sexpr_free (SHULLIVAN * shul, ITEM * item)
{
	ITEM * sub;

	assert (shul != NULL && item != NULL);

	if (item->it.itype == IT_IDENT) {
		(void)identFree (item->id.id);
		itemFree (shul, item);
		return;
	}

	assert (item->it.itype == IT_SLIST);
	sub = item->sl.first;
	itemFree (shul, item);
	while (sub != NULL) {
		item = sub->it.next;
		sexpr_free (shul, sub);
		sub = item;
	}
}

static void
sexpr_print (FILE * f, ITEM * item)
{
	char * spacer;

	assert (item != NULL);
	if (item->it.itype == IT_IDENT) {
		fprintf (f, "%s", item->id.id->name);
		return;
	}

	assert (item->it.itype == IT_SLIST);

	fprintf (f, "(");
	item = item->sl.first;
	spacer = "";
	while (item != NULL) {
		fprintf (f, "%s", spacer);
		sexpr_print (f, item);
		spacer = " ";
		item = item->it.next;
	}
	fprintf (f, ")");
}

static void
printHelp (void)
{
	printf (
"\nShullivan: an interactive Ghilbert proof checker\n\n"
"cd             - change directory\n"
"       cd DIRECTORY\n"
"def            - ghilbert definition\n"
"       def ((DEFID [VAR ...]) RHS)\n"
"defs           - list definitions\n"
"erase          - erase history item NUMBER and all subsequent items\n"
"       erase NUMBER\n"
"export         - verify an export .ghi Ghilbert interface file\n"
"       export (IFACEID path/to/basename ([PARAM_ID...]) \"PREFIX\")\n"
"flags        - set flags affecting shullivan operation\n"
"       flags NUMERIC_VALUE\n"
"history      - display history\n"
"import         - import a .ghi Ghilbert interface file\n"
"       import (IFACEID path/to/basename ([PARAM_ID...]) \"PREFIX\")\n"
"interfaces     - list imported interfaces\n"
"isave          - save history as a .ghi file\n"
"       isave (FILENAME [START_HISTNUM])\n"
"keep           - Toggle retention of proof steps.\n"
"kindbind       - kindbind with .gh file semantics\n"
"       kindbind (OLDKIND NEWKIND)\n"
"kinds          - list all kinds\n"
"load           - load a .gh Ghilbert proof file\n"
"       load path/to/basename\n"
"save           - save results to a file\n"
"       save (FILENAME [START_HISTNUM])\n"
"statements     - list statements\n"
"stats          - print various statistics\n"
"terms          - list terms\n"
"thm            - verify theorem\n"
"       thm (THMID ([(DVVAR1 ...) ...]) ([(HYPNAM HYP) ...])\n"
"                  {CONCL | ([CONCL ...])} (STEP ...))\n"
"undo           - undo last change (last history item)\n"
"var            - define variables\n"
"       var (KINDID VAR1 ...)\n"
"variables      - list variables\n"
"verbose        - set the verbosity level\n"
"       verbose NUMERIC_VALUE\n---\n"
"help           - print this message\n"
"exit           - exit shullivan\n\n"
		);
}

static void
scanCleanup (SCANNER * scan)
{
	if (scan->gb.buf != NULL) {
		free (scan->gb.buf);
		scan->gb.buf = NULL;
		scan->gb.size = 0;
		scan->idlen = 0;
	}

	if (scan->curline != NULL) {
		scan->free_line (scan->curline, scan, scan->ctx);
		scan->curline = 0;
		scan->len = 0;
		scan->ix = 0;
	}
}


typedef struct _FILE_SCANNER_CONTEXT {
	FILE * f;
	char * freebuf;
} FILE_SCANNER_CONTEXT;

#define FILE_SCAN_BUF_SIZE	(8192 + 1)
#define FILE_SCAN_BINARY	1

static char *
fileReadMore (SCANNER * scan, void * ctx)
{
	FILE_SCANNER_CONTEXT * fc = ctx;
	char * buf;
	size_t len;

	assert (scan != NULL && fc != NULL);

	buf = (char *)fc->freebuf;

	if (buf == NULL) {
		if ((buf = malloc (FILE_SCAN_BUF_SIZE)) == NULL) {
			perror ("fileReadMore:malloc");
			return NULL;
		}
	} else {
		fc->freebuf = *(char **)buf; /* next in list */
	}

	/* 
	 * scanToken() can handle the case that the buffer doesn't
	 * end the line, and can also handle embedded newlines.
	 */

#if FILE_SCAN_BINARY
	len = fread (buf, 1, FILE_SCAN_BUF_SIZE - 1, fc->f);

	if (len == 0) /* EOF or Error */
		return NULL;

	buf [len] = '\0'; /* ensure NUL-terminated. Odd behavior may
			     ensue if the file has embedded NUL's. */

	return buf;
#else
	/*
	 * fgets() returns NULL on EOF or error, otherwise it returns
	 * buf. When it returns buf, buf contains a NUL-terminated
	 * string.
	 *
	 * We could consider using fread() instead...
	 */

	return fgets (buf, FILE_SCAN_BUF_SIZE, fc->f);
#endif
}

static void
fileFreeLine (char * line, SCANNER * scan, void * ctx)
{
	FILE_SCANNER_CONTEXT * fc = ctx;

	assert (line != NULL && scan != NULL && fc != NULL);

	/* link the buffer on the free list */
	*(char **)line = fc->freebuf;
	fc->freebuf = line;
}

#define PATH_COMP_SEP '/'

static FILE *
tryPathOpen (char ** dirs, int ndirs, char * fname)
{
	FILE * f;
	int i;
	int len;
	char * path;
	int flen = strlen (fname);

	for (i = 0; i < ndirs; ++i) {
		len = strlen (dirs[i]);
		path = malloc (len + flen + 2);
		if (path == NULL)
			return NULL;
		memcpy (path, dirs[i], len);
		path[len] = PATH_COMP_SEP;
		memcpy (path + len + 1, fname, flen + 1);
		f = fopen (path, "r");

		free (path);

		if (f != NULL)
			return f;
	}

	return NULL;
}

static int
fileScannerInit (SHULLIVAN * shul, SCANNER * scan, 
		 char * name, const char * suffix)
{
	FILE * f;
	FILE_SCANNER_CONTEXT * ctx;
	char * fullname;
	int ret;

	assert (scan != NULL && name != NULL);

	fullname = name;
	if (suffix != NULL) {
		int len1 = strlen (name);
		int len2 = strlen (suffix);
		fullname = malloc (len1 + len2 + 1);
		if (fullname == NULL) {
			perror ("fileScannerInit:malloc");
			return -1;
		}
		memcpy (fullname, name, len1);
		memcpy (fullname + len1, suffix, len2 + 1);
	}

	/* Handle URL-style escapes like %20 for space ... */


	ret = -1;

	/*
	 * Try in current directory first, then try prepending
	 * directories in paths if fullname doesn't start with '/'.
	 */

	f = fopen (fullname, "r");
	if (f == NULL) {
		if (fullname[0] == PATH_COMP_SEP ||
		    (f = tryPathOpen (shul->path, shul->ndirs,
				      fullname)) == NULL) {
			perror ("fopen");
			fprintf (stderr, "Cannot open '%s'\n", fullname);
			goto fileScannerInit_done;
		}
	}

#if FILE_SCAN_BINARY
	/* 
	 * We use a fairly big application buffer in this
	 * case, so skip the stdio buffering.
	 */
	if (setvbuf (f, NULL, _IONBF, 0) != 0)
		perror ("warning: setvbuf");
#endif

	ctx = malloc (sizeof (*ctx));
	if (ctx == NULL) {
		perror ("fileScannerInit:malloc");
		fclose (f);
		goto fileScannerInit_done;
	}

	ctx->f = f;
	ctx->freebuf = NULL;

	scannerInit (scan, fileReadMore, ctx, fileFreeLine, scanToken,
		     NULL, scanCleanup);
	scan->lineno = 1;

	ret = 0;

fileScannerInit_done:
	if (fullname != name)
		free (fullname);

	return ret;
}

static void
fileScannerClose (SCANNER * scan)
{
	FILE_SCANNER_CONTEXT * ctx;
	char * buf;

	assert (scan != NULL && scan->ctx != NULL);

	ctx = scan->ctx;
	fclose (ctx->f);

	scan->cleanup (scan);

	while ((buf = ctx->freebuf) != NULL) {
		ctx->freebuf = *(char **)buf;
		free (buf);
	}

	scan->ctx = NULL; /* invalidate */
}

#define MAX_FLAT_DEPTH 2

static int
exprDepth (EXPR * exp)
{
	int max;
	int i;
	int depth;

	if (exp->ex.etype != ET_SEXPR)
		return 0;

	max = 0;
	for (i = 0; i < exp->sx.t->arity; ++i) {
		depth = exprDepth (exp->sx.args[i]);
		if (depth > max) {
			max = depth;
			if (depth >= MAX_FLAT_DEPTH)
				return depth + 1;
		}
	}

	return (max + 1);
}

static void
exprPrint (FILE * f, EXPR * exp, unsigned long verbose, int indent)
{
	int i;
	int depth;

	switch (exp->ex.etype) {
	case ET_IVAR:
		fprintf (f, "%s", exp->vi.id->name);
		break;
	case ET_SEXPR:
		fprintf (f, "(%s", exp->sx.t->sym.ident->name);
		if (verbose & SHUL_VERB_PRINT_PRETTY) {
			depth = exprDepth (exp); /* ugh, double recurse */
			if (depth <= MAX_FLAT_DEPTH)
				goto exprPrintFlat;

			indent += 2 + exp->sx.t->sym.ident->idlen;
			for (i = 0; i < exp->sx.t->arity; ++i) {
				if (i == 0)
					fprintf (f, " ");
				else
					fprintf (f, "\n%*s", indent, "");
				exprPrint (f, exp->sx.args[i], 
					   verbose, indent);
			}
		} else {
exprPrintFlat:
			for (i = 0; i < exp->sx.t->arity; ++i) {
				fprintf (f, " ");
				exprPrint (f, exp->sx.args[i], 
					   verbose, indent);
			}
		}
		fprintf (f, ")");
		break;
	case ET_VAR:
		fprintf (f, "%s", exp->var.sym.ident->name);
		break;
	default:
		assert (0);
		break;
	}
}

typedef struct _STATDVPRINT {
	STATEMENT * s;
	char ** space;
	FILE * f;
} STATDVPRINT;

void * dvPairPrint (int i, int j, void * ctx)
{
	STATDVPRINT * sp = ctx;

	fprintf (sp->f, "%s(%s %s)", *sp->space,
		 sp->s->vi[i].id->name, sp->s->vi[j].id->name);
	*sp->space = " ";

	return NULL;
}

static void *
dvEnumerate (int nvars, uint32_t * dvbits, DV_ENUMERATE_FUNC f, void * ctx)
{
	int npairs;
	void * res;
	uint32_t * word;
	uint32_t w;
	int i, j, k, n, z, p;

	word = dvbits;
	if (word == NULL)
		return NULL;

	npairs = nvars * (nvars - 1) / 2;

	k = 0;

	/* p(i,j) = i + sum {r | 0 <= r < j} = i + j * (j - 1) / 2 */
	j = 1;
	p = 0;

	while (k < npairs) {
		w = *word++;
		z = k - 1;
		while (w != 0) {
			/* ffs(w) is how many bits we need to shift
			 * right to clear the least significant bit
			 * in w.
			 */
			n = ffs (w);
			w >>= n;
			z += n;
			/* z is now the desired index. Find (i, j). */
			/* invariant: p <= z */
			while (p + j <= z) {
				p += j;
				++j;
			}
			i = z - p; /* i < j */

			res = f (i, j, ctx);
			if (res)
				return res;
		}
		k += 32;
	}
	return NULL;
}

#define PRINT_HISTNUM	1  /* applies to histPrint() */
#define PRINT_VERBOSE   1  /* applies to statementPrint() */
#define PRINT_AS_THM	2
#define ABBREV_PROOF	4
#define PRINT_AS_GHI	8
#define PRINT_ONLY_THM	16 /* applies to histPrint() */
#define PRINT_INTERNAL	32 /* applies to histPrint() */
#define PRINT_PRETTY	64
#define PRINT_DEF_AS_TERM 128  /* applies to histPrint() */
#define PRINT_MULT_CONC 256    /* always use multiple conclusion syntax */

static void
statementPrint (FILE * f, STATEMENT * s, unsigned long verbose)
{
	int indent;
	char * space;
	int i;
	STATDVPRINT sp;
	int j;
	unsigned long exprVerbose;

	if (verbose == 0) {
		fprintf (f, " %s", s->sym.ident->name);
		return;
	}

	indent = (verbose >> 16);
	verbose &= 0xffff;

	if ((verbose & PRINT_AS_THM) && s->thm == NULL)
		verbose &= ~PRINT_AS_THM;

	if (verbose & PRINT_AS_THM)
		indent += fprintf (f, "thm  (%s (", s->sym.ident->name);
	else
		indent += fprintf (f, "stmt (%s (", s->sym.ident->name);

	if (s->dvbits != NULL || (verbose & PRINT_PRETTY)) {
		space = "";
		sp.space = &space;
		sp.s = s;
		sp.f = f;
		dvEnumerate (s->nhvars + s->nWild, s->dvbits,
			     dvPairPrint, &sp);
		fprintf (f, ")\n%*s(", indent - 1, "");
	} else {
		indent += fprintf (f, ") (");
	}

	exprVerbose = (verbose & PRINT_PRETTY) ? SHUL_VERB_PRINT_PRETTY : 0;

	for (i = 0; i < s->nHyps; ++i) {
		if (i != 0) {
			if (verbose & PRINT_PRETTY)
				fprintf (f, "\n%*s", indent, "");
			else
				fprintf (f, " ");
		}
		if (verbose & PRINT_AS_THM) {
			j = fprintf (f, "(%s ", s->thm->hypnam[i]->name);
			exprPrint (f, s->hyps[i], exprVerbose, indent + j);
			fprintf (f, ")");
		} else
			exprPrint (f, s->hyps[i], exprVerbose, indent);
	}
	if (i != 0 || (verbose & PRINT_PRETTY) != 0)
		fprintf (f, ")\n%*s", indent - 1, "");
	else {
		indent += fprintf (f, ") ");
	}
	if (s->nCons != 1 || (verbose & PRINT_MULT_CONC) != 0)
		fprintf (f, "(");
	else
		indent--;

	for (i = 0; i < s->nCons; ++i) {
		if (i != 0) {
			if (verbose & PRINT_PRETTY)
				fprintf (f, "\n%*s", indent, "");
			else
				fprintf (f, " ");
		}
		exprPrint (f, s->cons[i], exprVerbose, indent);
	}
	if (s->nCons != 1 || (verbose & PRINT_MULT_CONC) != 0) {
		indent--;
		fprintf (f, ")");
	}
	if ((verbose & ABBREV_PROOF) != 0) {
		if (verbose & PRINT_PRETTY)
			fprintf (f, "\n%*s...", indent, "");
		else
			fprintf (f, " ...");
	} else if (verbose & PRINT_AS_THM) {
		THEOREM * t = s->thm;
		PROOF_STEP * s;
		fprintf (f, "\n%*s(", indent, "");
		space = "";
		for (i = 0; i < t->nSteps; ++i) {
			fprintf (f, "%s", space);
			space = " ";
			s = &t->steps[i];
			if (s->s.type == STEPT_EXPR)
				exprPrint (f, s->expr.x, 0, 0);
			else if (s->s.type == STEPT_REF)
				fprintf (f, "%s",
					 s->ref.stat->sym.ident->name);
			else if (s->s.type == STEPT_HYP)
				fprintf (f, "%s",
					 t->hypnam[s->hyp.index]->name);
		}
		fprintf (f, ")");
	}
	fprintf (f, ")\n");
}

typedef struct _STAT_PRINTME_CTX {
	INTERFACE * iface;
	unsigned long verbose;
} STAT_PRINTME_CTX;

static void *
statementPrintMe (void * ctx, MAP_ELEM * me)
{
	STAT_PRINTME_CTX * pmc = ctx;
	STATEMENT * stat = me->v.p;

	if (stat->sym.stype == ST_STMT && stat->iface == pmc->iface) {
		printf ("  ");
		statementPrint (stdout, stat, pmc->verbose);
	}

	return NULL;
}

static int
statementList (SHULLIVAN * shul, ITEM * ignored)
{
	unsigned long i;
	HISTORY_ITEM * hi;
	INTERFACE * iface;
	STAT_PRINTME_CTX pmc;

	pmc.verbose = PRINT_VERBOSE | (2 << 16); /* 2 spaces indent */
	if (shul->verbose & SHUL_VERB_PRINT_PRETTY)
		pmc.verbose |= PRINT_PRETTY;
	if (shul->flags & REQ_MULT_CONC_SYNTAX)
		pmc.verbose |= PRINT_MULT_CONC;

	for (i = 0; i < shul->histlen; ++i) {
		hi = &shul->history[i / HISTORY_CHUNK_SIZE]->
			h[i % HISTORY_CHUNK_SIZE];
		if (hi->htype == HT_THM)
			statementPrint (stdout, (STATEMENT *)hi->it, 
				pmc.verbose & 0xffff);
		else if (hi->htype == HT_IMPORT) {
			iface = hi->it;
			pmc.iface = iface;
			printf ("From %s :\n",
				iface->sym.ident->name);
			mappingEnumerate (shul->syms,
					  statementPrintMe, &pmc);
		}
	}
	return 0;
}

typedef struct _IMPORT_CONTEXT {
	INTERFACE * iface;
	MAPPING * localKinds;
	MAPPING * localSyms;
	MAPPING * localTerms;
	int paramIndex;
	char * paramPrefix; /* param handling prefix (temp) */
	int paramPfxlen;
	int importing;		/* 1 -> import, 0 -> export */
	int exportFail;		/* Indicates export failure (e.g. on missing
				   statement) but can continue the export */
	int keephist;		/* keep history */
	int def_just;		/* 1 for def_just, 0 for stmt */
} IMPORT_CONTEXT;

typedef int (*IMPORT_CMD_FUNC) (SHULLIVAN * shul, 
				ITEM * arg, IMPORT_CONTEXT * ctx);

typedef struct _EXPR_PARSE_CONTEXT {
	MAPPING * syms;
	MAPPING * terms;
	MAPPING * varIndex;
	EXPR_VARINFO * vars;
	int varsSize;
	GROWBUF * vargb;
	int nTermExps;
	int nDefExps;
	int nVarExps;
	char * pMem;
} EXPR_PARSE_CONTEXT;

static int
growParseVars (EXPR_PARSE_CONTEXT * pctx)
{
	int i = pctx->varsSize + 1;

	if (growBuf (pctx->vargb, i * sizeof (EXPR_VARINFO)) != 0)
		return -1;

	pctx->vars = pctx->vargb->buf;
	pctx->varsSize = pctx->vargb->size / sizeof (EXPR_VARINFO);

	return 0;
}

static int
exprParse1 (ITEM * exp, EXPR_PARSE_CONTEXT * pctx, KIND * kindKnown)
{
	MAP_ELEM * me;
	KIND * kind;
	int i;
	int ret;
	TERM * term;

	if (exp->it.itype == IT_IDENT) {
		/* variable */

		++pctx->nVarExps; /* one more variable EXP */

		i = pctx->varIndex->size;
		if (i >= pctx->varsSize && growParseVars (pctx) != 0) {
			perror ("exprParse1:growParseVars");
			return -1;
		}

		me = mapElemInsert (exp->id.id, pctx->varIndex);
		if (me == NULL) {
			ALLOC_ERR ();
			return -1;
		}

		if (me->v.i == -1) {	/* Newly added */
			me->v.i = i;
			pctx->vars[i].index = i;
			pctx->vars[i].id = exp->id.id;
			pctx->vars[i].ex.etype = ET_IVAR;
			/* don't increment refcount, we do that 
			   elsewhere */
			pctx->vars[i].ex.kind = kindKnown;
		} else {
			/* Previously seen */
			i = me->v.i;
			kind = pctx->vars[i].ex.kind;
			if (kind == NULL) {
				pctx->vars[i].ex.kind = kindKnown;
			} else if (kindKnown != NULL &&
				   kind->rep != kindKnown->rep) {
				fprintf (stderr,
					 "*** variable kind mismatch "
					 "for '%s'. Needed '%s', "
					 "already was '%s'.\n",
					 exp->id.id->name,
					 kindKnown->id->name,
					 kind->id->name);
				return -1;
			}
		}
	} else {
		assert (exp->it.itype == IT_SLIST);

		exp = exp->sl.first;
		if (exp == NULL) {
			fprintf (stderr, 
				 "*** Empty list without term symbol!"
				 "\n");
			return -1;
		}
		if (exp->it.itype != IT_IDENT) {
			fprintf (stderr,
				 "*** Expected term symbol, got list."
				 "\n");
			return -1;
		}
		term = mapVal (exp->id.id, pctx->terms);
		if (term == NULL) {
			fprintf (stderr,
				 "*** Unknown term '%s'.\n", 
				 exp->id.id->name);
			return -1;
		}

		if (kindKnown != NULL &&
		    term->kind->rep != kindKnown->rep) {
			fprintf (stderr,
				 "*** Needed kind '%s', but term '%s' "
				 "has kind '%s'\n",
				 kindKnown->id->name,
				 term->sym.ident->name,
				 term->kind->id->name);
			return -1;
		}

		if (term->sym.stype == ST_TERM)
			++pctx->nTermExps;
		else {
			assert (term->sym.stype == ST_DEF);
			++pctx->nDefExps;
		}

		i = 0;
		for (exp = exp->it.next; exp != NULL; 
		     exp = exp->it.next) {
			if (i >= term->arity) {
				fprintf (stderr,
					 "*** Excess arguments to term "
					 "'%s'\n",
					 term->sym.ident->name);
				return -1;
			}
			ret = exprParse1 (exp, pctx, term->kinds[i]);
			if (ret != 0)
				return ret;
			++i;
		}

		if (i < term->arity) {
			fprintf (stderr,
				 "*** Insufficient arguments to term "
				 "'%s'\n", term->sym.ident->name);
			return -1;
		}
	}

	return 0;
}

static EXPR *
exprParse2 (ITEM * exp, EXPR_PARSE_CONTEXT * pctx)
{
	int i;
	TERM * term;
	S_EXPR * sexpr;
	EXPR * ex;

	/* In the first pass we did all the checking, we don't
	 * need to check here. We do do some assertions, however.
	 */

	if (exp->it.itype == IT_IDENT) {
		ex = mapVal (exp->id.id, pctx->varIndex);
		assert (ex != NULL);
		return ex;
	} else {
		/* IT_SLIST */
		exp = exp->sl.first;
		assert (exp != NULL && exp->it.itype == IT_IDENT);
		term = mapVal (exp->id.id, pctx->terms);
		assert (term != NULL);
		sexpr = (S_EXPR *)pctx->pMem;
		sexpr->ex.etype = ET_SEXPR;
		sexpr->ex.kind = term->kind;
		sexpr->t = term;
		pctx->pMem = (char *)&sexpr->args[term->arity];

		exp = exp->it.next;

		for (i = 0; i < term->arity; ++i) {
			assert (exp != NULL);
			ex = exprParse2 (exp, pctx);
			assert (ex != NULL && 
				ex->ex.kind->rep == term->kinds[i]->rep);
			sexpr->args[i] = ex;
			exp = exp->it.next;
		}
		assert (exp == NULL);

		return (EXPR *)sexpr;
	}
}

/*
 * Check for variables with no kind inferred yet;
 * if any are found, check for a variable in localSyms
 * as a default choice for the kind. If not allowing
 * loose variable kinds, check that the inferred kind
 * matches the variable's declared kind for all <nvars>
 * variables in the <vars> array.
 */

static int
varDefaultKinds (EXPR_VARINFO * vars, int nvars, unsigned long loose,
		 MAPPING * syms)
{
	EXPR_VARINFO * vi;
	int i = nvars;
	SYMBOL * sym;
	VAR * var;

	while (i > 0) {
		--i;
		vi = &vars[i];

		if (loose && vi->ex.kind != NULL)
			continue;

		sym = mapVal (vi->id, syms);
		if (sym == NULL || sym->stype != ST_VAR) {
			fprintf (stderr,
				 "*** Cannot infer kind for "
				 "undeclared variable '%s'\n",
				 vi->id->name);
			return -1;
		}

		var = SYM2VAR (sym);

		assert (var->ex.kind != NULL);

		if (vi->ex.kind != NULL &&
		    vi->ex.kind->rep != var->ex.kind->rep) {
			/* Must not be loose */
			fprintf (stderr,
				 "*** kind mismatch for var '%s', "
				 "declared kind '%s', wanted '%s'\n",
				 vi->id->name,
				 var->ex.kind->id->name,
				 vi->ex.kind->id->name);
			return -1;
		}
		vi->ex.kind = var->ex.kind;
	}
	return 0;
}

static void *
varIndexRemap (void * ctx, MAP_ELEM * me)
{
	EXPR_VARINFO * vi = ctx;
	int i = me->v.i;

	me->v.p = vi + i; /* i.e. i --> &vi[i] */
	return NULL;
}

/*
 * Initialize all of EXPR_PARSE_CONTEXT except for ec->terms and ec->syms.
 */
static void
exprParseCtxInit (EXPR_PARSE_CONTEXT * ec, SHULLIVAN * shul)
{
	ec->vars = shul->vi.buf;
	ec->varsSize = shul->vi.size / sizeof (EXPR_VARINFO);
	ec->vargb = &shul->vi;
	ec->nTermExps = 0;
	ec->nDefExps = 0;
	ec->nVarExps = 0;
	ec->pMem = 0;

	ec->varIndex = shul->varIndex;

	assert (ec->varIndex->size == 0);
	ec->varIndex->defval.i = -1; /* set default value */
}

typedef struct _STATEMENT_PARSE_CONTEXT {
	EXPR_PARSE_CONTEXT ec;
	INTERFACE * iface;
	MAPPING * hypnams;
	ITEM * proofStepItem; /* out, only if hypnams != NULL */
	ITEM * hypItem;	      /* out, only if hypnams != NULL */
	int def_just;	      /* true if it's a definition justification */
} STATEMENT_PARSE_CONTEXT;

/*
 * parseStatement() handles both 'stmt' and 'thm', creating and
 * returning a STATEMENT *, but does not enter the STATEMENT into
 * the symbol table (although it does check that there is not a name
 * collision), and in the context of 'thm' does not check the proof.
 *
 * Within the <ctx> argument, hypnams and iface will be set
 * by the caller.  For a 'stmt', hypnams is NULL, for a 'thm', it
 * is an empty mapping on entry.
 * ctx->ec.terms and ctx->ec.syms must be set by the caller,
 * the other members of ctx->ec are initialized here.  On successful
 * return, ctx->ex.varIndex contains the variable-name to index variable
 * mapping for the statment. On an unsuccessful return, both
 * ctx->ex.varIndex and ctx->hypnams will be NULL (ctx->hypnams will
 * have been deleted if provided).
 */

static STATEMENT *
parseStatement (SHULLIVAN * shul, ITEM * arg,
		STATEMENT_PARSE_CONTEXT * ctx)
{
	ITEM * nameItem;
	ITEM * dvItem;
	ITEM * hypItem;
	ITEM * hypnamItem;
	ITEM * item;
	ITEM * item2;
	ITEM * concItem;
	ITEM * proofItem;
	ITEM * concStop;
	ITEM * djv1Item = NULL; /* compiler warning */
	ITEM * djv2Item;
	IDENT * pid;
	MAP_ELEM * me;
	size_t size;
	size_t bmap_size = 0; /* avoid gcc warning, not really necessary */
	int nhyps;
	int nconcs;
	int nWild;
	int nvars;
	TERM * term;
	int i;
	int j;
	int k;
	STATEMENT * stat;
	char * pMem;
	MAPPING * hypnams = ctx->hypnams;
	VAR * djvar1;
	VAR * djvar2;

	if (arg->it.itype != IT_SLIST ||
	    (nameItem = arg->sl.first) == NULL ||
	    nameItem->it.itype != IT_IDENT)
		goto parseStmtUsage;

	if (ctx->def_just) {
		SYMBOL * sym1;
		SYMBOL * sym2;

		if ((djv1Item = nameItem->it.next) == NULL ||
		    djv1Item->it.itype != IT_IDENT ||
		    (djv2Item = djv1Item->it.next) == NULL ||
		    djv2Item->it.itype != IT_IDENT ||
		    djv1Item->id.id == djv2Item->id.id ||
		    (dvItem = djv2Item->it.next) == NULL ||
		    dvItem->it.itype != IT_SLIST ||
		    (hypItem = dvItem->it.next) == NULL ||
		    hypItem->it.itype != IT_SLIST ||
		    (concItem = hypItem->it.next) != NULL)
			goto parseStmtUsage;

		/* Check that both def-just vars exist as variables of
		   the same kind. */

		if ((sym1 = mapVal (djv1Item->id.id, ctx->ec.syms)) == NULL ||
		    sym1->stype != ST_VAR ||
		    (sym2 = mapVal (djv2Item->id.id, ctx->ec.syms)) == NULL ||
		    sym2->stype != ST_VAR)
			goto parseStmtUsage;
		
		djvar1 = SYM2VAR (sym1);
		djvar2 = SYM2VAR (sym2);
		if (djvar1->ex.kind->rep != djvar2->ex.kind->rep) {
			fprintf (stderr, 
				 "Kind mismatch for def_just variables %s, %s "
				 "in %s\n", 
				 djv1Item->id.id->name, djv2Item->id.id->name,
				 nameItem->id.id->name);
			return NULL;
		}
		proofItem = NULL; /* for compiler warning */

	} else if ((dvItem = nameItem->it.next) == NULL ||
	    dvItem->it.itype != IT_SLIST ||
	    (hypItem = dvItem->it.next) == NULL ||
	    hypItem->it.itype != IT_SLIST ||
	    (concItem = hypItem->it.next) == NULL ||
	    (!hypnams && (proofItem = concItem->it.next) != NULL) ||
	    (hypnams && ((proofItem = concItem->it.next) == NULL ||
			 proofItem->it.itype != IT_SLIST ||
			 proofItem->it.next != NULL))) {

parseStmtUsage:
		if (ctx->def_just)
			fprintf (stderr, "*** expected def_just "
				 "(NAME DJVAR1 DJVAR2 ([(VAR1 VAR2 ...)]) "
				 "([(HYPNAME HYP) ...]))\n");
		else if (hypnams)
			fprintf (stderr,
			   "*** expected thm (NAME ([(VAR1 VAR2 ...)]) "
			   "([(HYPNAME HYP) ...]) "
			   "{CONCL | ([CONCL ...])} (STEP ...))\n");
		else
			fprintf (stderr,
			   "*** expected stmt (NAME ([(VAR1 VAR2 ...)]) "
			   "([HYP ...]) {CONCL | ([CONCL ...])})\n");
		
		return NULL;
	}

	if (hypnams) {
		if (shul->verbose & SHUL_VERB_PROGRESS) {
			printf ("verifying %s\n", nameItem->id.id->name);
			fflush (stdout);
		}
		ctx->proofStepItem = proofItem->sl.first;
		ctx->hypItem = hypItem->sl.first;
	}

	/*
	 * Note, we don't insert the theorem symbol yet, so that
	 * it can't be used in its own proof (or partially 
	 * initialized in its own definition, for a 'stmt').
	 */

	if (mapVal (nameItem->id.id, ctx->ec.syms) != NULL) {
		fprintf (stderr, "*** symbol '%s' already exists.\n",
			 nameItem->id.id->name);
		return NULL;
	}

	if (ctx->iface != NULL) {
		pid = identPrefixed (ctx->iface->prefix,
				     ctx->iface->pfxlen,
				     nameItem->id.id);
		if (pid == NULL) {
			perror ("parseStatement:identPrefixed");
			return NULL;
		}
		/*
		 * Check ALSO in shul->syms for the prefixed name.
		 */
		if (mapVal (pid, shul->syms) != NULL) {
			fprintf (stderr, "*** symbol '%s' already exists.\n",
				 pid->name);
			goto parseStatement_bad1;
		}
	} else {
		pid = nameItem->id.id;
		pid->refcount++;
	}

	/*
	 * ctx->ec.terms and ctx->ec.syms are set by the caller,
	 * we initialize the rest of ctx->ec.
	 */
	exprParseCtxInit (&ctx->ec, shul);

	nhyps = 0;
	for (item = hypItem->sl.first;
	     item != NULL;
	     item = item->it.next) {
		item2 = item;
		if (hypnams != NULL) {
			if (item->it.itype != IT_SLIST ||
			    (hypnamItem = item->sl.first) == NULL ||
			    hypnamItem->it.itype != IT_IDENT ||
			    (item2 = hypnamItem->it.next) == NULL ||
			    item2->it.next != NULL) {
				fprintf (stderr,
				 "*** Malformed hypothesis ident/expr "
				 "pair.\n");
				goto parseStatement_bad2;
			}
			me = mapElemInsert (hypnamItem->id.id,
					    hypnams);
			if (me == NULL) {
				ALLOC_ERR ();
				goto parseStatement_bad2;
			}
			if (me->v.i != -1) {
				fprintf (stderr,
				 "*** Hypothesis name '%s' occurs "
				 "twice.\n", hypnamItem->id.id->name);
				goto parseStatement_bad2;
			}
			me->v.i = nhyps;
			hypnamItem->id.id->refcount++;
		}
		if (exprParse1 (item2, &ctx->ec, NULL) != 0)
			goto parseStatement_bad2;
		++nhyps;
	}

	nWild = ctx->ec.varIndex->size; /* fix up later */

	/* Definition justification case: 2 'conclusions' */
	if (djv1Item != NULL) {
		concItem = djv1Item;
		concStop = dvItem;
		goto parseStatement_do_concs;
	}

	/* Check for old 1-conclusion syntax */

	concStop = NULL;

	if (concItem->it.itype == IT_IDENT) {
		if ((shul->flags & REQ_MULT_CONC_SYNTAX) != 0) {
			fprintf (stderr, "*** Multiple conclusions syntax is "
				 "required.\n");
			goto parseStatement_bad2;
		}
		goto oldConcSyntax;
	}

	assert (concItem->it.itype == IT_SLIST);

	item = concItem->sl.first;

	/* Note, 0 conclusions is allowed, e.g. 'drop'. */

	if ((shul->flags & REQ_MULT_CONC_SYNTAX) == 0 &&
	    item != NULL && item->it.itype == IT_IDENT &&
	    (term = mapVal (item->id.id, ctx->ec.terms))
	    != NULL) {

oldConcSyntax:
		/* 
		 * Using the old 1-conclusion syntax.
		 * Fix it up for the new multi-conclusion
		 * syntax. Note that concItem->it.next will
		 * be non-NULL in the thm case, but NULL in
		 * the statement case.
		 */
		concStop = concItem->it.next;
	} else {
		if ((shul->flags & MULTIPLE_CONCLUSIONS) == 0) {
			if (item != NULL && item->it.itype == IT_IDENT)
				fprintf (stderr,
					 "*** Multiple conclusions syntax is "
					 "disallowed, and term '%s' is not "
					 "known.\n", item->id.id->name);
			else
				fprintf (stderr,
					 "*** Multiple conclusions syntax is "
					 "disallowed.\n");
			goto parseStatement_bad2;
		}
		concItem = item;
	}

	/* process the conclusions */

parseStatement_do_concs:

	nconcs = 0;
	for (item = concItem; item != concStop; item = item->it.next) {
		if (exprParse1 (item, &ctx->ec, NULL) != 0)
			goto parseStatement_bad2;
		++nconcs;
	}

	nvars = ctx->ec.varIndex->size;

	nWild = nvars - nWild; /* now correct */

	/*
	 * OK, check for variables with no kind inferred yet;
	 * if any are found, check for a variable in localSyms
	 * as a default choice for the kind. If not allowing
	 * loose variable kinds, check that the inferred kind
	 * matches the variable's declared kind.
	 */

	if (varDefaultKinds (ctx->ec.vars, nvars,
			     (shul->flags & LOOSE_VAR_KINDS),
			     ctx->ec.syms) != 0)
		goto parseStatement_bad2;

	/*
	 * At this point we know all the variables used in the
	 * hypotheses or conclusions, and their kinds. We know
	 * the numbers of hypotheses and conclusions, and we
	 * know how big their expressions are in total. So
	 * we're ready to allocate memory for the statement.
	 */

	size = (offsetof (STATEMENT, vi) + 
		nvars * sizeof (EXPR_VARINFO) +
		(ctx->ec.nTermExps + ctx->ec.nDefExps) *
		 (offsetof (S_EXPR, args) + sizeof (EXPR *)) +
		ctx->ec.nVarExps * sizeof (EXPR *));

	dvItem = dvItem->sl.first;

	if (dvItem != NULL) {
		/*
		 * If any DV items were provided, we use a bitmap
		 * to represent the distinct variable conditions.
		 */
		int pairs = (nvars * (nvars - 1)) / 2;
		bmap_size = BIT_MAP_SIZE(pairs);
		size += bmap_size;
	}

	stat = calloc (1, size);
	if (stat == NULL) {
		perror ("parseStatement:calloc");
		goto parseStatement_bad2;
	}

	stat->sym.stype = ctx->def_just ? ST_DEFJUST : ST_STMT;
	stat->sym.ident = pid;
	stat->nHyps = nhyps;
	stat->nCons= nconcs;
	stat->nWild = nWild;
	stat->iface = ctx->iface;
	stat->nhvars = nvars - nWild;

	for (i = 0; i < nvars; ++i) {
		stat->vi[i] = ctx->ec.vars[i];
		stat->vi[i].id->refcount++; /* hang on to it */
	}

	pMem = (char *) &stat->vi[nvars];

	stat->thm = NULL;

	stat->dvbits = NULL;
	if (dvItem != NULL) {
		stat->dvbits = (uint32_t *)pMem;
		pMem += bmap_size;
	}

	stat->hyps = (EXPR **)pMem;
	pMem += nhyps * sizeof (EXPR *);
	stat->cons = (EXPR **)pMem;
	pMem += nconcs * sizeof (EXPR *);

	/*
	 * Ok, distinct variable conditions. Note that all bits
	 * default to zero due to the clearing in the calloc() of
	 * stat.
	 */

	for (; dvItem != NULL;
	     dvItem = dvItem->it.next) {
		if (dvItem->it.itype != IT_SLIST) {
			fprintf (stderr,
				 "*** Non-list item in DVC list\n");
			goto parseStatement_bad3;
		}
		/* The variables */
		for (item = dvItem->sl.first;
		     item != NULL;
		     item = item->it.next) {
			if (item->it.itype != IT_IDENT) {
				fprintf (stderr,
					 "*** Expected variable in DV "
					 "list\n");
				goto parseStatement_bad3;
			}
			i = mapValI (item->id.id, ctx->ec.varIndex);

			/* 
			 * Ignore DV conditions involving variables
			 * which do not occur in the hypotheses or
			 * conclusions. Should we instead call this
			 * an error?
			 */
			if (i == -1)
				continue;

			for (item2 = item->it.next;
			     item2 != NULL;
			     item2 = item2->it.next) {

				int m, n;

				if (item2->it.itype != IT_IDENT)
					continue; /* we'll catch the
						     error later */
				
				j = mapValI (item2->id.id, ctx->ec.varIndex);

				if (j == -1)
					continue;

				if (j == i) {
					fprintf (stderr,
					 "*** '%s' occurs twice in DV "
						 "list\n",
						item->id.id->name);
					goto parseStatement_bad3;
				}
				/* get indices in order */
				m = i;
				n = j;
				if (j < i) {
					n = i;
					m = j;
				}
				k = PAIRNUM (m, n);
				BIT_SET (stat->dvbits, k);
			}
			
		}
	}

	/* 
	 * Change varIndex to map from id to &stat->vi[i] instead of
	 * from id to i.  This is needed for theorem proving, when we
	 * use varIndex to map not only the variables which occur in the
	 * hypotheses and conclusions, but also other variables which
	 * occur in the proof, to handle distinct variable conditions
	 * involving remnant variables bound to definition dummies.
	 */

	ctx->ec.varIndex->defval.p = NULL;
	(void)mappingEnumerate (ctx->ec.varIndex, varIndexRemap, stat->vi);

	/* 
	 * Now we construct the actual expressions for the
	 * hypotheses and conclusions in the memory starting at
	 * pMem.
	 */

	ctx->ec.pMem = pMem;

	i = 0;
	for (item = hypItem->sl.first;
	     item != NULL;
	     item = item->it.next) {
		item2 = item;
		if (hypnams != NULL) {
			assert (item->it.itype == IT_SLIST &&
				item->sl.first != NULL &&
				item->sl.first->it.next != NULL);
			item2 = item->sl.first->it.next;
		}
		stat->hyps[i] = exprParse2 (item2, &ctx->ec);
		assert (stat->hyps[i] != NULL);
		++i;
	}

	i = 0;
	for (item = concItem;
	     item != concStop;
	     item = item->it.next) {
		stat->cons[i] = exprParse2 (item, &ctx->ec);
		assert (stat->cons[i] != NULL);
		++i;
	}

	assert (ctx->ec.pMem = (char *)stat + size);

	/*
	 * The caller will delete ctx->ec.varIndex when done with
	 * it; in the case of thm handling, it is still needed.
	 */

	return stat;

parseStatement_bad3:

	/* clean up stat */

	for (i = 0; i < nvars; ++i)
		stat->vi[i].id->refcount--; /* release idents */

	free (stat);

parseStatement_bad2:
	if (ctx->hypnams) {
		identTableDelete (ctx->hypnams);
		ctx->hypnams = NULL;
	}

	/* clean up ctx */

	mappingEmpty (ctx->ec.varIndex, NULL, NULL);
	ctx->ec.varIndex = NULL;

parseStatement_bad1:
	identFree (pid);
	return NULL;

}

static int
exprCheck (ITEM * item, EXPR * exp, EXPR_PARSE_CONTEXT * ctx, KIND * knownKind)
{
	ITEM * termItem;
	int i;
	TERM * t;
	TERM * t2;
	IDENT * id;
	MAP_ELEM * me;

#if 0
	fprintf (stderr, "exprCheck ");
	sexpr_print (stderr, item);
	fprintf (stderr, "  vs.  ");
	exprPrint (stderr, exp, 0, 0);
	fprintf (stderr, "\n");
#endif

	if (exp->ex.etype == ET_SEXPR) {
		if (item->it.itype != IT_SLIST ||
		    (termItem = item->sl.first) == NULL ||
		    termItem->it.itype != IT_IDENT) {
			fprintf (stderr,
				 "*** Required term, provided ");
			sexpr_print (stderr, item);
			fprintf (stderr, "\n");
			return -1;
		}
		t = exp->sx.t;
		/* Check that the term used has already been exported */

		t2 = mapVal (termItem->id.id, ctx->terms);

		if (t2 == NULL) {
			fprintf (stderr,
				 "*** Term %s not exported yet.\n",
				termItem->id.id->name);
			return -1;
		}

		if (t2 != t) {
			fprintf (stderr,
				 "*** Term mismatch, wanted %s got %s.\n",
				 t->sym.ident->name, termItem->id.id->name);
			return -1;
		}
		
		item = termItem->it.next;
		for (i = 0; i < t->arity; ++i) {
			if (item == NULL) {
				fprintf (stderr,
					 "*** Insufficient arguments provided "
					 "for term %s\n",
					 termItem->id.id->name);
				return -1;
			}
			if (exprCheck (item, exp->sx.args[i], 
				       ctx, t->kinds[i]) != 0)
				return -1;

			item = item->it.next;
		}
		if (item != NULL) {
				fprintf (stderr,
					 "*** Excess arguments provided "
					 "for term %s\n",
					 termItem->id.id->name);
				return -1;
		}
		return 0;
	}

	assert (exp->ex.etype == ET_IVAR);

	if (item->it.itype != IT_IDENT) {
		fprintf (stderr,
			 "*** Required variable, provided ");
		sexpr_print (stderr, item);
		fprintf (stderr, "\n");
		return -1;
	}

	id = item->id.id;

	i = exp->vi.index;

	if (ctx->vars[i].id == NULL) {
		/* note, indices are in order of occurrence in hypotheses
		 * then conclusions.
		 */
		assert (ctx->varIndex->size == i);

		ctx->vars[i].id = id;

		/* 
		 * The mapping isn't indispensible here, but we use it
		 * when checking the DV conditions also.
		 */

		me = mapElemInsert (id, ctx->varIndex);
		if (me == NULL) {
			ALLOC_ERR ();
			return -1;
		}
		if (me->v.i != -1) {
			fprintf (stderr,
				 "*** Variable %s bound twice.",
				 id->name);
			return -1;
		}
		me->v.i = i;
		if (ctx->vars[i].ex.kind == NULL) {
			ctx->vars[i].ex.kind = knownKind;
		     /* assert (knownKind == NULL || 
				knownKind == exp->vi.ex.kind); */
		}
		return 0;
	}

	if (ctx->vars[i].id == id) {
		if (ctx->vars[i].ex.kind == NULL) {
			ctx->vars[i].ex.kind = knownKind;
		     /* assert (knownKind == NULL || 
				knownKind == exp->vi.ex.kind); */
		}
		return 0;
	}

	fprintf (stderr,
		 "*** Variables %s and %s both used for original %s\n",
		 ctx->vars[i].id->name, id->name, exp->vi.id->name);
	return -1;
}

typedef struct _EXDVC {
	uint32_t * dvbits;
	int bad;
	char * msg;
	EXPR_VARINFO * vi;
	char * statName;
} EXDVC;

static void *
exportDvCheck (int i, int j, void * ctx)
{
	EXDVC * dv = ctx;

	if (dv->dvbits == NULL ||
	    BIT (dv->dvbits, PAIRNUM(i, j)) == 0) {
		if (!dv->bad)
			fprintf (stderr, "%s: %s", dv->statName, dv->msg);
		dv->bad = 1;
		fprintf (stderr, " (%s %s)",
			 dv->vi[i].id->name,
			 dv->vi[j].id->name);
	}
	return NULL;
}

/*
 * This routine frees a statement whose identifier has already been
 * removed from the symbol table (but the identifier still needs
 * freeing itself).
 */
static void
statementFree (STATEMENT * stat)
{
	int i;
	THEOREM * thm;

	assert (stat != NULL && stat->sym.ident != NULL);
	if ((thm = stat->thm) != NULL) {
		for (i = 0; i < stat->nHyps; ++i)
			identFree (thm->hypnam[i]);
		free (thm->steps);
		free (thm);
	}
	identFree (stat->sym.ident);
	i = stat->nhvars + stat->nWild;
	while (i > 0) {
		--i;
		identFree (stat->vi[i].id);
	}
	free (stat);
}

static int
import_stmt (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ctx)
{
	STATEMENT * stat;
	STATEMENT_PARSE_CONTEXT sctx;
	MAP_ELEM * me;

	sctx.ec.terms = ctx->localTerms;
	sctx.ec.syms = ctx->localSyms;
	sctx.iface = ctx->iface;
	sctx.hypnams = NULL; /* no hypothesis names for a 'stmt' */
	sctx.def_just = 0;

	stat = parseStatement (shul, arg, &sctx);
	if (stat == NULL)
		return -1;

	mappingEmpty (sctx.ec.varIndex, NULL, NULL);

	me = mapElemInsert (stat->sym.ident, shul->syms);
	if (me == NULL) {
		ALLOC_ERR ();
		statementFree (stat);
		return -1;
	}

	/*
	 * parseStatement() checked that there was no existing
	 * statement of the same name.
	 */
	assert (me->v.p == (void *)NULL);

	me->v.p = stat;

	return 0;
}

static int
import_def_just (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ctx)
{
	STATEMENT * stat;
	STATEMENT_PARSE_CONTEXT sctx;
	MAP_ELEM * me;

	if ((shul->flags & DEF_JUSTIFY) == 0) {
		fprintf (stderr, "'def_just' is not allowed unless the "
			 "DEF_JUSTIFY flag is enabled.\n");
		return -1;
	}
	sctx.ec.terms = ctx->localTerms;
	sctx.ec.syms = ctx->localSyms;
	sctx.iface = ctx->iface;
	sctx.hypnams = NULL; /* no hypothesis names for a 'def_just' */
	sctx.def_just = 1;

	stat = parseStatement (shul, arg, &sctx);
	if (stat == NULL)
		return -1;

	mappingEmpty (sctx.ec.varIndex, NULL, NULL);

	me = mapElemInsert (stat->sym.ident, shul->syms);
	if (me == NULL) {
		ALLOC_ERR ();
		statementFree (stat);
		return -1;
	}

	/*
	 * parseStatement() checked that there was no existing
	 * statement of the same name.
	 */
	assert (me->v.p == (void *)NULL);

	me->v.p = stat;

	return 0;
}

static void
idPrintMe (void * ctx, MAP_ELEM * me)
{
	IDENT * id = me->obj;
	FILE * f = ctx;
	fprintf (f, " %s", id->name);
}

static void *
idPrint (void * ctx, MAP_ELEM * me)
{
	IDENT * id = me->obj;
	FILE * f = ctx;
	fprintf (f, " %s", id->name);
	return NULL;
}

static int
export_stmt (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ictx)
{
	STATEMENT * stat;
	STATEMENT_PARSE_CONTEXT ctx;
	ITEM * nameItem;
	ITEM * dvItem;
	ITEM * hypItem;
	ITEM * item;
	ITEM * concItem;
	ITEM * concStop;
	ITEM * djv1Item = NULL;
	ITEM * djv2Item;
	IDENT * pid;
	int nvars;
	TERM * term;
	int i;
	int j;
	int k;
	EXDVC exdvc;
	uint32_t * dvbits;
	int cycle;
	DVWORK * dvw = NULL; /* avoid compiler warning */
	unsigned long warndv;
	VAR * djvar1;
	VAR * djvar2;

	ctx.ec.terms = ictx->localTerms;
	ctx.ec.syms = ictx->localSyms;
	ctx.iface = ictx->iface;

	if (arg->it.itype != IT_SLIST ||
	    (nameItem = arg->sl.first) == NULL ||
	    nameItem->it.itype != IT_IDENT)
		goto export_stmt_usage;

	if (ictx->def_just) {
		SYMBOL * sym1;
		SYMBOL * sym2;

		if ((djv1Item = nameItem->it.next) == NULL ||
		    djv1Item->it.itype != IT_IDENT ||
		    (djv2Item = djv1Item->it.next) == NULL ||
		    djv2Item->it.itype != IT_IDENT ||
		    djv1Item->id.id == djv2Item->id.id ||
		    (dvItem = djv2Item->it.next) == NULL ||
		    dvItem->it.itype != IT_SLIST ||
		    (hypItem = dvItem->it.next) == NULL ||
		    hypItem->it.itype != IT_SLIST ||
		    (concItem = hypItem->it.next) != NULL)
			goto export_stmt_usage;

		if ((sym1 = mapVal (djv1Item->id.id, ctx.ec.syms)) == NULL ||
		    sym1->stype != ST_VAR ||
		    (sym2 = mapVal (djv2Item->id.id, ctx.ec.syms)) == NULL ||
		    sym2->stype != ST_VAR)
			goto export_stmt_usage;
		
		djvar1 = SYM2VAR (sym1);
		djvar2 = SYM2VAR (sym2);
		concItem = djv1Item;
		concStop = dvItem;

	} else if ((dvItem = nameItem->it.next) == NULL ||
		   dvItem->it.itype != IT_SLIST ||
		   (hypItem = dvItem->it.next) == NULL ||
		   hypItem->it.itype != IT_SLIST ||
		   (concItem = hypItem->it.next) == NULL ||
		   (concStop = concItem->it.next) != NULL) {
export_stmt_usage:
		if (ictx->def_just)
			fprintf (stderr,
				 "*** expected def_just "
				 "(NAME ([(VAR1 VAR2 ...)]) ([HYP ...]))\n");
		else
			fprintf (stderr,
				 "*** expected stmt (NAME ([(VAR1 VAR2 ...)]) "
				 "([HYP ...]) {CONCL | ([CONCL ...])})\n");
		return -1;
	}

	pid = identPrefixed (ctx.iface->prefix,
			     ctx.iface->pfxlen,
			     nameItem->id.id);
	if (pid == NULL) {
		ALLOC_ERR ();
		return -1;
	}

	stat = mapVal (pid, shul->syms);

	if (stat == NULL || 
	    stat->sym.stype != (djv1Item ? ST_DEFJUST : ST_STMT)) {
		fprintf (stderr, "*** statement '%s' does not exist.\n",
			 pid->name);
		identFree (pid);
#if 0
		return -1;
#else
		ictx->exportFail = 1;
		return 0;
#endif
	}

	identFree (pid); /* don't need it anymore */

	/* quick hypothesis count */
	i = 0;
	for (item = hypItem->sl.first; item != NULL; item = item->it.next)
		++i;

	if (i != stat->nHyps) {
		fprintf (stderr,
			 "*** statement '%s' has %d hypotheses, but "
			 "exported with %d\n",
			 stat->sym.ident->name, stat->nHyps, i);
		return -1;
	}

	if (djv1Item != NULL)
		goto export_stmt_haveconcs;

	/* Check for old 1-conclusion syntax */

	if (concItem->it.itype != IT_IDENT) {

		assert (concItem->it.itype == IT_SLIST);

		item = concItem->sl.first;

		/* Note, 0 conclusions is allowed, e.g. 'drop'. */

		if ((shul->flags & REQ_MULT_CONC_SYNTAX) != 0 ||
		    item == NULL || item->it.itype != IT_IDENT ||
		    (term = mapVal (item->id.id, ctx.ec.terms)) == NULL) {
			if ((shul->flags & MULTIPLE_CONCLUSIONS) == 0) {
				if (item != NULL && item->it.itype == IT_IDENT)
					fprintf (stderr,
						 "*** Multiple conclusions "
						 "syntax is disallowed, and "
						 "term '%s' is not known.\n",
						 item->id.id->name);
				else
					fprintf (stderr,
						 "*** Multiple conclusions "
						 "syntax is disallowed.\n");
				return -1;
			}
			concItem = item;
		}
	} else if ((shul->flags & REQ_MULT_CONC_SYNTAX) != 0) {
		fprintf (stderr,
			 "*** Multiple conclusions syntax is required "
			 "for statement %s\n", stat->sym.ident->name);
		return -1;
	}

	/* quick count of conclusions */

	i = 0;
	for (item = concItem; item != NULL; item = item->it.next)
		++i;

	if (i != stat->nCons) {
		fprintf (stderr,
			 "*** statement '%s' has %d conclusions, but "
			 "exported with %d\n",
			 stat->sym.ident->name, stat->nCons, i);
		return -1;
	}

export_stmt_haveconcs:

	/*
	 * ctx.ec.terms and ctx.ec.syms are set by the caller,
	 * we initialize the rest of ctx.ec (or that part which we need).
	 */

	nvars = stat->nhvars + stat->nWild;

	/* 
	 * shul->vi was used when parsing the statement originally,
	 * and it never shrinks, so it should be big enough now.
	 */

	assert (nvars * sizeof (EXPR_VARINFO) <= shul->vi.size);

	ctx.ec.vars = shul->vi.buf;

	for (i = 0; i < nvars; ++i) {
		ctx.ec.vars[i].id = NULL;
		ctx.ec.vars[i].ex.kind = NULL;
	}

#if 0 /* not needed */
	ctx.ec.varsSize = shul->vi.size / sizeof (EXPR_VARINFO);
	ctx.ec.vargb = &shul->vi;
	ctx.ec.nTermExps = 0;
	ctx.ec.nDefExps = 0;
	ctx.ec.nVarExps = 0;
	ctx.ec.pMem = 0;
#endif

	ctx.ec.varIndex = shul->varIndex;
	assert (ctx.ec.varIndex->size == 0);
	ctx.ec.varIndex->defval.i = -1; /* set default value */


	/*
	 * To check that the provided hypotheses and conclusions match
	 * those of the existing statement, we need:
	 * - A mapping to look up identifiers used as variables in
	 *   the provided hypotheses or conclusions.  This allows us to
	 *   check that the same identifier is not mapped to different
	 *   variables from the existing statement.
	 * - A reverse look-up array from the existing statement's variables
	 *   to the new identifiers.  This lets us stop immediately if
	 *   more than one identifier gets mapped to the same existing
	 *   statement variable, rather than just counting at the end.
	 */

	i = 0;
	for (item = hypItem->sl.first; item != NULL; item = item->it.next) {
		if (exprCheck (item, stat->hyps[i], &ctx.ec, NULL) != 0)
			goto export_stmt_bad;
		++i;
	}

	assert (stat->nhvars == ctx.ec.varIndex->size);

	/* process the conclusions */

	i = 0;
	for (item = concItem; item != concStop; item = item->it.next) {
		if (exprCheck (item, stat->cons[i], &ctx.ec, NULL) != 0)
			goto export_stmt_bad;
		++i;
	}

	assert (nvars == ctx.ec.varIndex->size);

	/*
	 * OK, check for variables with no kind inferred yet;
	 * if any are found, check for a variable in localSyms
	 * as a default choice for the kind. If not allowing
	 * loose variable kinds, check that the inferred kind
	 * matches the variable's declared kind.
	 */

	if (varDefaultKinds (ctx.ec.vars, nvars,
			     (shul->flags & EXPORT_LOOSE_VAR_KINDS),
			     ctx.ec.syms) != 0)
		goto export_stmt_bad;

	/*
	 * Ugh. We still need to check that all variables have the
	 * expected kinds, since some formal variable arguments might
	 * have received their kinds not by inference from terms but by
	 * default from the kind of the named local variable. (This can
	 * occur regardless of whether loose variable kinds are allowed.)
	 * (Note, this also checks the kinds of the def_just vars for
	 * def_just commands.)
	 */

	for (i = 0; i < nvars; ++i) {
		if (ctx.ec.vars[i].ex.kind->rep != stat->vi[i].ex.kind->rep) {
			fprintf (stderr,
				 "*** Kind mismatch for variable %s (is %s, "
				 "needed %s)\n", ctx.ec.vars[i].id->name,
				 ctx.ec.vars[i].ex.kind->id->name,
				 stat->vi[i].ex.kind->id->name);
		}
	}

	dvItem = dvItem->sl.first;

	if (nvars > shul->ndvvars) {
		int dvsize;
		/*
		 * If any DV items were provided, we use a bitmap
		 * to represent the distinct variable conditions.
		 */
		int pairs = (nvars * (nvars - 1)) / 2;
		dvsize = BIT_MAP_SIZE(pairs);
		dvbits = calloc (1, dvsize);
		if (dvbits == NULL) {
			ALLOC_ERR ();
			goto export_stmt_bad;
		}
		shul->dvsize = dvsize;
		free (shul->dvbits);
		shul->dvbits = dvbits;
	}

	dvbits = shul->dvbits;

	/* Validate distinct variable conditions. */

	if ((warndv = (shul->flags & EXPORT_WARN_DV)) != 0)
		assert (shul->fvi->size == 0);

	for (; dvItem != NULL;
	     dvItem = dvItem->it.next) {
		if (dvItem->it.itype != IT_SLIST) {
			fprintf (stderr,
				 "*** Non-list item in DVC list\n");
			goto export_stmt_bad;
		}
		j = 0;
		for (item = dvItem->sl.first;
		     item != NULL;
		     item = item->it.next) {
			if (item->it.itype != IT_IDENT) {
				fprintf (stderr,
					 "*** Expected variable in DV "
					 "list\n");
				goto export_stmt_bad;
			}
			i = mapValI (item->id.id, ctx.ec.varIndex);
			if (i == -1) {
				/* remember for warning message */
				if (warndv)
					(void) mapElemInsert (item->id.id,
							      shul->fvi);
				continue;
			}
			if (j * sizeof (DVWORK) > shul->dvw.size &&
			    growBuf (&shul->dvw, j * sizeof (DVWORK)) != 0) {
				ALLOC_ERR ();
				goto export_stmt_bad;
			}
			dvw = shul->dvw.buf;
			dvw[j].i = i;
			dvw[j].id = item->id.id;
			++j;
		}
		cycle = j;
		for (i = 0; i < cycle - 1; ++i) {
			for (j = i + 1; j < cycle; ++j) {
				int m, n;
				m = dvw[i].i;
				n = dvw[j].i;
				if (m == n) {
					fprintf (stderr,
						 "*** '%s' occurs twice in DV "
						 "list\n",
						 dvw[i].id->name);
					goto export_stmt_bad;
				}
				if (n < m) {
					k = m;
					m = n;
					n = k;
				}
				k = PAIRNUM (m, n);
				BIT_SET (dvbits, k);
			}
		}
	}

	if (warndv && shul->fvi->size != 0) {
		fprintf (stderr, "%s : Warning: Variables (",
			nameItem->id.id->name);
		mappingEmpty (shul->fvi, idPrintMe, stderr);
		fprintf (stderr, " ) occur in DV but not hypotheses or "
			 "conclusions.\n");
	}

	/* 
	 * Ok, now check that the provided DV pairs contain at least
	 * those required for the original statement.
	 */

	exdvc.vi = ctx.ec.vars;
	exdvc.dvbits = dvbits;
	exdvc.bad = 0;
	exdvc.msg = "*** Missing DV pairs (";
	exdvc.statName = nameItem->id.id->name;

	(void) dvEnumerate (nvars, stat->dvbits, exportDvCheck, &exdvc);
	if (exdvc.bad) {
		fprintf (stderr, " )\n");
		goto export_stmt_bad;
	}

	/*
	 * Now warn if the export specified additional unneeded
	 * DV conditions...
	 */

	if (warndv) {
		exdvc.dvbits = stat->dvbits;
		exdvc.msg = "Warning: unneeded DV pairs (";

		(void) dvEnumerate (nvars, dvbits, exportDvCheck, &exdvc);
		if (exdvc.bad) {
			/* Not really bad, just a warning. */
			fprintf (stderr, " )\n");
		}
	}

	nvars = nvars * (nvars - 1) / 2;
	memset (dvbits, 0, BIT_MAP_SIZE (nvars));

	mappingEmpty (ctx.ec.varIndex, NULL, NULL);

	return 0;


export_stmt_bad:

	mappingEmpty (shul->fvi, NULL, NULL);

	memset (shul->dvbits, 0, shul->dvsize);

	/* clean up varIndex */

	mappingEmpty (ctx.ec.varIndex, NULL, NULL);

	return -1;
}

static int
export_def_just (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ictx)
{
	int result;
	if ((shul->flags & DEF_JUSTIFY) == 0) {
		fprintf (stderr, 
			 "*** def_just encountered in export but "
			 "DEF_JUSTIFY option is not enabled.\n");
#if 0
		return -1;
#else
		ictx->exportFail = 1;
		return 0;
#endif
	}
	ictx->def_just = 1;
	result = export_stmt (shul, arg, ictx);
	ictx->def_just = 0; /* restore usual value -- ugh */
	return result;
}

#define VAR_CHUNK 64

static struct _VAR_ALLOC {
	VAR * free;
	unsigned long n;
	unsigned long nFree;
} var_alloc = {0};

static VAR * 
varAlloc (void)
{
	VAR * v;
	int i;

	v = var_alloc.free;
	if (v == NULL) {
		v = malloc (VAR_CHUNK * sizeof (*v));
		if (v == NULL)
			return NULL;
		i = VAR_CHUNK - 1;
		v[i].ex.kind = NULL;
		while (i > 0) {
			v[i-1].ex.kind = (KIND *)&v[i];
			--i;
		}
		var_alloc.n += VAR_CHUNK;
		var_alloc.nFree = VAR_CHUNK;
	}
	var_alloc.free = (VAR *)v->ex.kind;
	var_alloc.nFree --;
	return v;
}

static void
varFree (VAR * var)
{
	var->ex.kind = (KIND *)var_alloc.free;
	var_alloc.free = var;
	var_alloc.nFree ++;
}

static int
import_var (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ctx)
{
	ITEM * kindItem;
	ITEM * varItem;
	KIND * kind;
	KIND * oldkind;
	VAR * var;
	IDENT * id;
	MAP_ELEM * me;

	if (arg->it.itype != IT_SLIST ||
	    (kindItem = arg->sl.first) == NULL ||
	    kindItem->it.itype != IT_IDENT) {
import_var_format:
		fprintf (stderr, 
			 "*** expected var (KIND [VAR ...]))"
			 "\n");
		return -1;
	}

	kind = mapVal (kindItem->id.id, ctx->localKinds);
	if (kind == NULL) {
		fprintf (stderr,
			 "*** unknown variable kind '%s'\n",
			 kindItem->id.id->name);
		return -1;
	}

	for (varItem = kindItem->it.next;
	     varItem != NULL;
	     varItem = varItem->it.next) {

		if (varItem->it.itype != IT_IDENT)
			goto import_var_format;

		id = varItem->id.id;

		var = varAlloc();
		if (var == NULL) {
			perror ("import_var:malloc");
			return -1;
		}

		var->ex.etype = ET_VAR;
		var->ex.kind = kind;
		var->sym.ident = id;
		var->sym.stype = ST_VAR;

		me = mapElemInsert (id, ctx->localSyms);
		if (me == NULL) {
			ALLOC_ERR ();
			varFree (var);
			return -1;
		}

		if (me->v.p != NULL) {
			SYMBOL * sym = me->v.p;
			varFree (var);
			if (sym->stype != ST_VAR) {
				assert (sym->stype == ST_STMT);
				fprintf (stderr, "*** name '%s' already exists"
					 " as statement.\n", id->name);
				return -1;
			}
			if ((shul->flags & LOOSE_VAR_KINDS) == 0) {
				fprintf (stderr,
					 "*** variable '%s' already "
					 "added.\n", id->name);
				return -1;
			}
			var = SYM2VAR(sym);
			oldkind = var->ex.kind;
			var->ex.kind = kind; /* change kind */
		} else {
			oldkind = NULL;
			me->v.p = &var->sym;
			id->refcount ++;
		}
		if (ctx->keephist) {
			if (histAdd (shul, HT_VAROLDKIND,  oldkind) != 0)
				goto import_var_bad1;
			if (histAdd (shul, HT_VARNEWKIND, kind) != 0) {
				shul->histlen --;
				goto import_var_bad1;
			}
			if (histAdd (shul, HT_VAR, var) != 0) {
				shul->histlen -= 2;
				goto import_var_bad1;
			}
		}
	}

	return 0;

import_var_bad1:
	if (oldkind == NULL) {
		id->refcount--;
		varFree (var);
	}
	return -1;
}

static int
import_term (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ctx)
{
	ITEM * kindItem;
	ITEM * termItem;
	ITEM * termIdItem;
	ITEM * argItem;
	KIND * tkind;
	KIND * kind;
	TERM * term;
	IDENT * pid;
	MAP_ELEM * me;
	INTERFACE * iface = ctx->iface;
	int arity;

	if (arg->it.itype != IT_SLIST ||
	    (kindItem = arg->sl.first) == NULL ||
	    kindItem->it.itype != IT_IDENT) {
import_term_format:
		fprintf (stderr, 
			 "*** expected term (KIND (TERMID [KIND ...]) ...)"
			 "\n");
		return -1;
	}

	tkind = mapVal (kindItem->id.id, ctx->localKinds);
	if (tkind == NULL) {
		fprintf (stderr,
			 "*** unknown term result kind '%s'\n",
			 kindItem->id.id->name);
		return -1;
	}

	for (termItem = kindItem->it.next;
	     termItem != NULL;
	     termItem = termItem->it.next) {

		if (termItem->it.itype != IT_SLIST ||
		    (termIdItem = termItem->sl.first) == NULL ||
		    termIdItem->it.itype != IT_IDENT)
			goto import_term_format;

		/* count the arguments */

		arity = 0;

		for (argItem = termIdItem->it.next;
		     argItem != NULL;
		     argItem = argItem->it.next) {

			if (argItem->it.itype != IT_IDENT)
				goto import_term_format;
			++arity;
		}
		pid = identPrefixed (iface->prefix, iface->pfxlen,
				     termIdItem->id.id);
		if (pid == NULL) {
			perror ("import_term:identPrefixed");
			return -1;
		}

		term = mapVal (pid, shul->terms);

		if (ctx->importing) {

			if (term != NULL) {
				fprintf (stderr,
					 "*** term '%s' already exists.\n",
					 pid->name);
				goto import_term_bad1;
			}
	
			term = malloc (sizeof (*term) + 
				       arity * sizeof (KIND *));
			if (term == NULL) {
				perror ("import_term:malloc");
				goto import_term_bad1;
			}

			term->sym.ident = pid;
			term->sym.stype = ST_TERM;
			term->iface = iface;
			term->arity = arity;
			term->kind = tkind;
			term->kinds = (KIND **)(term + 1);

			me = mapElemInsert (pid, shul->terms);
			if (me == NULL) {
				ALLOC_ERR ();
				goto import_term_bad2;
			}
			/* must be new, we checked earlier */
			assert (me->v.p == NULL);
			me->v.p = term;
			/* We've already got a reference count on pid from
			   identPrefixed() */

		} else {
			if (term == NULL) {
				fprintf (stderr,
					 "*** exported term '%s' not found.\n",
					 pid->name);
				goto import_term_bad1;
			}
			identFree (pid); /* exporting, don't need it anymore */
		}


		/* check and save kinds */
		arity = 0;

		for (argItem = termIdItem->it.next;
		     argItem != NULL;
		     argItem = argItem->it.next) {
			kind = mapVal (argItem->id.id, ctx->localKinds);
			if (kind == NULL) {
				fprintf (stderr,
					 "*** formal term arg '%s' is not a "
					 "kind.\n", argItem->id.id->name);
				if (ctx->importing)
					goto import_term_bad3;
				return -1;
			}
			if (ctx->importing)
				term->kinds[arity] = kind;
			else if (term->kinds[arity]->rep != kind->rep) {
				/*
				 * XXX: What if the kinds are equivalent
				 * in shul, but the export .ghi file hasn't
				 * specified the corresponding kindbind yet,
				 * so that the kinds wouldn't be equivalent
				 * if the .ghi was later imported?
				 */
				fprintf (stderr,
					 "*** kind mismatch for arg %d of "
					 "exported term %s\n", arity,
					term->sym.ident->name);
				return -1;
			}
			++arity;
		}

		me = mapElemInsert (termIdItem->id.id, ctx->localTerms);
		if (me == NULL) {
			ALLOC_ERR ();
			if (ctx->importing)
				goto import_term_bad3;
			return -1; /* already freed pid */
		}
		if (me->v.p != NULL) {
			fprintf (stderr,
				 "*** A local term %s already exists.\n",
				 termIdItem->id.id->name);

			/* localTerms will be cleaned up in port() */
			if (ctx->importing)
				goto import_term_bad3;
			return -1;
		}
		me->v.p = term;
		termIdItem->id.id->refcount++;

		/* 
		 * Save the identifier without the prefix in a map for
		 * later imports.
		 */
		me = mapElemInsert (termIdItem->id.id, iface->terms);
		if (me == NULL) {
			ALLOC_ERR ();
			if (ctx->importing)
				goto import_term_bad3;
			return -1; /* already freed pid */
		}
		assert (me->v.p == NULL);
		me->v.p = term;
		termIdItem->id.id->refcount++;
	}
	
	return 0; /* Success! */

	/* import_term_bad3, import_term_bad2 are only used when importing */

import_term_bad3:
	mapElemDelete (pid, shul->terms);
import_term_bad2:
	free (term);
import_term_bad1:
	(void)identFree (pid);
	return -1;
}

static int
import_kind (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ctx)
{
	ITEM * item;
	IDENT * pid;
	KIND * kind;
	INTERFACE * iface = ctx->iface;
	MAP_ELEM * me;

	if (arg->it.itype != IT_SLIST) {
		fprintf (stderr, "*** 'kind' expects list argument\n");
		return -1;
	}

	/* Hmm, actually, gh_verify.py allows just one kind here... */

	item = arg->sl.first;
	for (item = arg->sl.first; item != NULL; item = item->it.next) {
		if (item->it.itype != IT_IDENT) {
			fprintf (stderr, "*** 'kind' expects list of "
				 "identifiers\n");
			return -1;
		}
		/* Note, pid may be just item->id.id if the prefix is
		   empty */
		pid = identPrefixed (iface->prefix,
				     iface->pfxlen, item->id.id);
		if (pid == NULL) {
			perror ("import_kind:identPrefixed");
			return -1;
		}

		if (ctx->importing) {
			kind = malloc (sizeof (*kind));
			if (kind == NULL) {
				perror ("import_kind:malloc");
				goto import_kind_bad1;
			}

			me = mapElemInsert (pid, shul->kinds);
			if (me == NULL) {
				ALLOC_ERR ();
				goto import_kind_bad2;
			}
			if (me->v.p != NULL) {
				fprintf (stderr, "*** kind %s already "
					 "present\n", pid->name);
				goto import_kind_bad2;
			}
			me->v.p = kind;
			/* We got a reference count from identPrefixed(). */

			kind->id = pid;
			kind->iface = iface;
			kind->rep = kind;   /* initially in class by itself */
		} else {
			/* exporting */
			kind = mapVal (pid, shul->kinds);
			if (kind == NULL) {
				fprintf (stderr, "*** exported kind %s does "
					 "not exist.\n", pid->name);
				goto import_kind_bad1;
			}
			/* exporting, don't need the prefixed ID any more */
			identFree (pid);
		}

		me = mapElemInsert (item->id.id, ctx->localKinds);
		if (me == NULL)
			return -1;

		assert (me->v.p == NULL); /* must be new */
		me->v.p = kind;
		item->id.id->refcount++;

		/*
		 * iface->kinds records kinds provided by this import.
		 * ctx->localKinds includes also local kinds added
		 * via 'param' directives.
		 */
		me = mapElemInsert (item->id.id, iface->kinds);
		if (me == NULL)
			return -1;

		assert (me->v.p == NULL); /* must be new */
		me->v.p = kind;
		item->id.id->refcount++;
	}
	return 0;

import_kind_bad2:
	free (kind);
import_kind_bad1:
	(void)identFree (pid);
	return -1;
}

typedef struct _KINDBIND_CONTEXT {
	KIND * k1;
	KIND * k2;
} KINDBIND_CONTEXT;

static void *
kindJoin (void * ctx, MAP_ELEM * me)
{
	KINDBIND_CONTEXT * kb = (KINDBIND_CONTEXT *) ctx;
	KIND * k = me->v.p;

	if (k->rep == kb->k2)
		k->rep = kb->k1;
	return NULL;
}

static int
import_kindbind (SHULLIVAN * shul, ITEM * arg, IMPORT_CONTEXT * ctx)
{
	ITEM * k1Item;
	ITEM * k2Item;
	KINDBIND_CONTEXT kb;
	KIND * k1;
	KIND * k2;
	char * kname;

	if (arg->it.itype != IT_SLIST ||
	    (k1Item = arg->sl.first) == NULL ||
	    k1Item->it.itype != IT_IDENT ||
	    (k2Item = k1Item->it.next) == NULL ||
	    k2Item->it.itype != IT_IDENT ||
	    k2Item->it.next != NULL) {
		fprintf (stderr,
			 "*** 'kindbind' expects (kind1 kind2)\n");
		return -1;
	}

	assert (k1Item->id.id != NULL && k2Item->id.id != NULL);

	kname = k1Item->id.id->name;
	if ((k1 = mapVal (k1Item->id.id, ctx->localKinds)) == NULL) {

import_kindbind_badkind:
		fprintf (stderr,
			 "*** kind '%s' not known.\n",
			 kname);
		return -1;

	}

	kname = k2Item->id.id->name;
	if ((k2 = mapVal (k2Item->id.id, ctx->localKinds)) == NULL)
		goto import_kindbind_badkind;

	/*
	 * Check if the two kinds are already equivalent. If so,
	 * do nothing.
	 */
	if (k1->rep == k2->rep)
		return 0;

	if (!ctx->importing) {
		fprintf (stderr,
			 "*** export kindbind kinds not equivalent "
			 "(%s vs %s)\n",
			 k1->id->name, k2->id->name);
		return -1;
	}

	/* 
         * The kind with the smaller representative address should be
	 * in kb.k1; it will be the new representative for all kinds
	 * whose current representative is either k1 or k2.
	 */

	if (k2->rep < k1->rep) {
		kb.k1 = k2->rep;
		kb.k2 = k1->rep;
	} else {
		kb.k1 = k1->rep;
		kb.k2 = k2->rep;
	}

	/* Join the two kind equivalence classes */
	mappingEnumerate (shul->kinds, kindJoin, &kb);

	return 0;
}

static void *
kindAdopt (void * arg, MAP_ELEM * me)
{
	IMPORT_CONTEXT * ctx = arg;
	IDENT * pid;
	IDENT * kindId = me->obj;
	KIND * kind = me->v.p;
	MAP_ELEM * kme;

	pid = identPrefixed (ctx->paramPrefix,
			     ctx->paramPfxlen, kindId);
	if (pid == NULL) {
		perror ("kindAdopt:identPrefixed");
		return me; /* non-NULL for failure */
	}

	/*
	 * Add the kind from the previous import to localKinds
	 * but not ctx->iface->kinds.
	 */
	kme = mapElemInsert (pid, ctx->localKinds);
	if (kme == NULL) {
		(void)identFree (pid);
		ALLOC_ERR ();
		return me; /* fail */
	}

	assert (kme->v.p == NULL); /* must be new */

	kme->v.p = kind;
	/* identPrefixed() incremented the reference count */

	return NULL;
}

static void *
termAdopt (void * arg, MAP_ELEM * me)
{
	IMPORT_CONTEXT * ctx = arg;
	IDENT * pid;
	IDENT * termId = me->obj;
	TERM * term = me->v.p;
	MAP_ELEM * tme;

	pid = identPrefixed (ctx->paramPrefix, ctx->paramPfxlen,
			     termId);
	if (pid == NULL) {
		perror ("termAdopt:identPrefixed");
		return me; /* non-NULL for failure */
	}

	/*
	 * We add the mapping to localTerms but not iface->terms,
	 * so that it does not pollute later imports.
	 */
	tme = mapElemInsert (pid, ctx->localTerms);
	if (tme == NULL) {
		(void)identFree (pid);
		ALLOC_ERR ();
		return me; /* fail */
	}

	assert (tme->v.p == NULL); /* must be new */

	tme->v.p = term;
	/* pid already has the reference count we need */

	return NULL;
}

static int
import_param (SHULLIVAN * shul, ITEM * args, IMPORT_CONTEXT * ctx)
{
	ITEM * nameItem;	/* unused now */
	ITEM * fileItem;	/* unused now */
	ITEM * paramsItem;	/* unused now */
	ITEM * prefixItem;
	IDENT * id;
	INTERFACE * paramIf;
	char * pfxsrc;
	int pfxlen;

	/* 
	 * This import needs to refer to the kinds and terms
	 * from earlier imports.
	 */

	if (args->it.itype != IT_SLIST ||
	    (nameItem = args->sl.first) == NULL ||
	    nameItem->it.itype != IT_IDENT ||
	    (fileItem = nameItem->it.next) == NULL ||
	    fileItem->it.itype != IT_IDENT ||
	    (paramsItem = fileItem->it.next) == NULL ||
	    paramsItem->it.itype != IT_SLIST ||
	    (prefixItem = paramsItem->it.next) == NULL ||
	    prefixItem->it.itype != IT_IDENT ||
	    prefixItem->it.next != NULL) {
		fprintf (stderr, "*** Malformed param s-expression\n");
		return -1;
	}

	id = prefixItem->id.id;
	pfxlen = id->idlen;
	pfxsrc = id->name;
	if (id->name[0] == '"' && id->name[pfxlen - 1] == '"') {
		if (pfxlen == 1)
			pfxlen = 0;
		else
			pfxlen -= 2;
		pfxsrc += 1;
	}

	if (pfxlen == 0)
		ctx->paramPrefix = NULL;
	else {
		if ((ctx->paramPrefix = malloc (pfxlen + 1)) == NULL) {
			perror ("import_param:malloc");
			return -1;
		}
		memcpy (ctx->paramPrefix, pfxsrc, pfxlen);
		ctx->paramPrefix[pfxlen] = '\0';
	}
	ctx->paramPfxlen = pfxlen;

	if (ctx->paramIndex >= ctx->iface->nparams) {
		fprintf (stderr, 
			 "Insufficient parameters provided "
			 "for interface (have %d, want more)\n",
			ctx->iface->nparams);
		goto import_param_bad1;
	}
	paramIf = ctx->iface->params[ctx->paramIndex++];

	if (mappingEnumerate (paramIf->kinds, kindAdopt, ctx) != NULL)
		goto import_param_bad1;

	if (mappingEnumerate (paramIf->terms, termAdopt, ctx) != NULL)
		goto import_param_bad1;

	free (ctx->paramPrefix); /* NULL ok */
	return 0;

import_param_bad1:
	free (ctx->paramPrefix); /* NULL ok */
	return -1;
}

static void
localVarFree (void * ctx, MAP_ELEM * me)
{
	IDENT * id = me->obj;
	VAR * var = SYM2VAR (me->v.p);

	varFree (var);
	(void)identFree (id);
}

typedef int (*CMD_FUNC) (SHULLIVAN * shul, ITEM * arg, void * ctx);

typedef CMD_FUNC (*FIND_CMD_FUNC) (char *);

static int
fileProcess (SHULLIVAN * shul, ITEM * fileItem,
	     char * extension, char * dbgPrefix,
	     FIND_CMD_FUNC find, void * ctx)
{
	int res;
	SCANNER scan;
	ITEM * item;
	char * cmd;
	CMD_FUNC cmdFunc;

	if (fileScannerInit (shul, &scan, fileItem->id.id->name, 
			     extension) != 0)
		return -1;

	for (;;) {
		res = scan.get_token (&scan);

		if (res == SCAN_ERR) {
			perror ("get_token returned SCAN_ERR");
			res = -1;
			goto fileCleanup;
		}


		if (res == SCAN_EOF)
			break;

		if (res == SCAN_LPAREN) {
			fprintf (stderr, 
				 "\nOops, expected a command but got "
				 "'('\nIgnoring until matching ')'..."
				 "\n");
			for (;;) {
				item = read_sexpr (shul, &scan);
				if (item == NULL) {
					fprintf (stderr,
						 "EOF while searching "
						"for ')'\n");
					res = -1;
					goto fileCleanup;
				}
				sexpr_free (shul, item);
			}
			continue;
		}

		if (res == SCAN_RPAREN) {
			fprintf (stderr, "Oops, expected a command "
				 "but got ')'\n");
			continue;
		}

		cmd = scan.gb.buf;

		cmdFunc = find (cmd);
		if (cmdFunc == NULL) {
			fprintf (stderr, "%s unknown command %s\n",
				 dbgPrefix, cmd);
			res = -1;
			goto fileCleanup;
		}

		if (shul->verbose & SHUL_VERB_COMMANDS) {
			printf ("%s %s ", dbgPrefix, cmd);
		}

		if ( (item = read_sexpr (shul, &scan)) == NULL) {
			fprintf (stderr, "Bad s-expression\n");
			res = -1;
			goto fileCleanup;
		}

		if (shul->verbose & SHUL_VERB_COMMANDS) {
			sexpr_print (stdout, item);
			printf ("\n");
		}

		res = cmdFunc (shul, item, ctx);

		sexpr_free (shul, item);

		if (res != 0)
			goto fileCleanup;
	}

	res = 0; /* success */

fileCleanup:

	if (res != 0)
		fprintf (stderr, "%s last line number: %d\n",
			 dbgPrefix, scan.lineno);

	fileScannerClose (&scan);
	return res;
	
}

static CMD_FUNC
importFindFunc (char * cmd)
{
	IMPORT_CMD_FUNC cmdFunc;

	if (strcmp (cmd, "stmt") == 0)
		cmdFunc = import_stmt;
	else if (strcmp (cmd, "term") == 0)
		cmdFunc = import_term;
	else if (strcmp (cmd, "var") == 0)
		cmdFunc = import_var;
	else if (strcmp (cmd, "kind") == 0)
		cmdFunc = import_kind;
	else if (strcmp (cmd, "kindbind") == 0)
		cmdFunc = import_kindbind;
	else if (strcmp (cmd, "param") == 0)
		cmdFunc = import_param;
	else if (strcmp (cmd, "def_just") == 0) /* only if DEF_JUSTIFY ? */
		cmdFunc = import_def_just;
	else {
		cmdFunc = NULL;
	}
	return (CMD_FUNC)cmdFunc;
}

static CMD_FUNC
exportFindFunc (char * cmd)
{
	IMPORT_CMD_FUNC cmdFunc;

	if (strcmp (cmd, "stmt") == 0)
		cmdFunc = export_stmt;
	else if (strcmp (cmd, "term") == 0)
		cmdFunc = import_term;
	else if (strcmp (cmd, "var") == 0)
		cmdFunc = import_var;
	else if (strcmp (cmd, "kind") == 0)
		cmdFunc = import_kind;
	else if (strcmp (cmd, "kindbind") == 0)
		cmdFunc = import_kindbind;
	else if (strcmp (cmd, "param") == 0)
		cmdFunc = import_param;
	else if (strcmp (cmd, "def_just") == 0)
		cmdFunc = export_def_just;
	else {
		cmdFunc = NULL;
	}
	return (CMD_FUNC)cmdFunc;
}

static void *
recordOrigKindRep (void * ctx, MAP_ELEM * me)
{
	MAPPING * map = (MAPPING *) ctx;
	KIND * kind = me->v.p;
	MAP_ELEM * newme;

	newme = mapElemInsert (kind, map);
	if (newme == NULL)
		return me; /* Arbitrary non-NULL to stop walk &
			      indicate error */

	newme->v.p = kind->rep; /* save original class representative */
	return NULL;
}

static void *
restoreOrigKindRep (void * ctx, MAP_ELEM * me)
{
	KIND * kind = me->obj;
	kind->rep = me->v.p;
	return NULL;
}

static int
import (SHULLIVAN * shul, ITEM * args)
{
	return port (shul, args, 1 /* importing */);
}

static int
export (SHULLIVAN * shul, ITEM * args)
{
	return port (shul, args, 0 /* exporting */);
}

static int
port (SHULLIVAN * shul, ITEM * args, int importing)
{
	ITEM * nameItem;
	ITEM * fileItem;
	ITEM * paramsItem;
	ITEM * prefixItem;
	ITEM * param;
	IDENT * id;
	MAP_ELEM * me;
	int nparams;
	int ret;
	INTERFACE * iface;
	INTERFACE * paramIf;
	INTERFACE ** paramIfaces;
	IMPORT_CONTEXT ctx;
	char * pfxsrc;
	int pfxlen;
	
	assert (shul != NULL && args != NULL);

	if (args->it.itype != IT_SLIST ||
	    (nameItem = args->sl.first) == NULL ||
	    nameItem->it.itype != IT_IDENT ||
	    (fileItem = nameItem->it.next) == NULL ||
	    fileItem->it.itype != IT_IDENT ||
	    (paramsItem = fileItem->it.next) == NULL ||
	    paramsItem->it.itype != IT_SLIST ||
	    (prefixItem = paramsItem->it.next) == NULL ||
	    prefixItem->it.itype != IT_IDENT ||
	    prefixItem->it.next != NULL) {
		fprintf (stderr, "*** Malformed import/export s-expression\n");
		return -1;
	}
	if (shul->verbose & SHUL_VERB_PROGRESS) {
		printf ("%sporting %s\n", importing ? "Im" : "Ex",
			 nameItem->id.id->name);
		fflush (stdout);
	}

	iface = calloc (1, sizeof (*iface));
	if (iface == NULL) {
		perror ("calloc");
		return -1;
	}

	ctx.localTerms = NULL;  /* prevent premature cleanup */
	ctx.localSyms = NULL;
	ctx.localKinds = NULL;

	iface->fileId = fileItem->id.id;
	iface->fileId->refcount++;

	me = mapElemInsert (nameItem->id.id, shul->interfaces);
	if (me == NULL) {
		ALLOC_ERR ();
		goto port_bad;
	}

	if (me->v.p != NULL) {
		fprintf (stderr,
			 "*** Interface named %s already present.\n",
			nameItem->id.id->name);
		goto port_bad;
	}
	me->v.p = iface;

	nameItem->id.id->refcount++;
	iface->sym.ident = nameItem->id.id;
	iface->sym.stype = ST_INTERFACE;

	/*
	 * Kinds provided by this interface. Lookup by local (unprefixed)
	 * identifiers.
	 */
	if ((iface->kinds = mappingCreate(NULL)) == NULL)
		goto port_bad;

	/*
	 * Terms provided by this interface.
	 * Temporarily also holds the local names of terms
	 * obtained via param from other interfaces, but these
	 * are removed at the end of the import/export.
	 */
	if ((iface->terms = mappingCreate(NULL)) == NULL)
		goto port_bad;

	ctx.iface = iface;
	/*
	 * All kinds used locally by this interface, including those
	 * obtained from 'param'.
	 */
	if ((ctx.localKinds = mappingCreate(NULL)) == NULL)
		goto port_bad;

	/*
	 * Variables exported by this interface.
	 */
	if ((ctx.localSyms = mappingCreate(NULL)) == NULL)
		goto port_bad;

	/*
	 * All terms used by this interface, including those obtained
	 * from 'param'.
	 */
	if ((ctx.localTerms = mappingCreate(NULL)) == NULL)
		goto port_bad;

	ctx.paramIndex = 0;
	ctx.importing = importing;
	ctx.exportFail = 0;
	ctx.keephist = 0;
	ctx.def_just = 0;

	param = paramsItem->sl.first;
	nparams = 0;

	while (param != NULL) {
		if (param->it.itype != IT_IDENT) {
			fprintf (stderr,
				 "*** Each interface parameter must be "
				 "an identifier naming an already "
				 "imported/exported interface.\n");
			goto port_bad;
		}
		++nparams;
		param = param->it.next;
	}

	paramIfaces = malloc (nparams * sizeof (*paramIfaces));
	if (paramIfaces == NULL) {
		perror ("malloc");
		goto port_bad;
	}

	iface->nparams = nparams;
	iface->params = paramIfaces;

	for (nparams = 0, param = paramsItem->sl.first;
	     param != NULL;
	     param = param->it.next, ++nparams) {
		paramIf = mapVal (param->id.id, shul->interfaces);
		if (paramIf == NULL) {
			fprintf (stderr, 
				 "Parameter interface '%s' "
				 "not found.\n", param->id.id->name);
			goto port_bad;
		}
		assert (paramIf->sym.stype == ST_INTERFACE);

		paramIfaces[nparams] = paramIf;
	}

	/*
	 * Now that we're interning identifiers immediately, it's
	 * not cool to modify the ident name string in place.
	 * Make a copy.
	 */


	id = prefixItem->id.id;
	pfxlen = id->idlen;
	pfxsrc = id->name;

	assert (pfxlen >= 1);

	/*
	 * I think ghilbert allows a prefix consisting of a single
	 * double-quote character as another means of specifying an
	 * empty prefix string.
	 */
	if (id->name[0] == '"' && id->name[pfxlen - 1] == '"') {
		if (pfxlen == 1)
			pfxlen = 0;
		else
			pfxlen -= 2;
		pfxsrc += 1;
	}

	if (pfxlen == 0)
		iface->prefix = NULL;
	else {
		iface->prefix = malloc (pfxlen + 1);
		if (iface->prefix == NULL)
			goto port_bad;
		memcpy (iface->prefix, pfxsrc, pfxlen);
		iface->prefix[pfxlen] = '\0';
	}
	iface->pfxlen = pfxlen;

	if (importing) {
		/*
		 * Save original kind equivalence class representatives in case
		 * we need to back out kindbinds from a failing import.
		 * Export kindbinds don't change anything, so there's no
		 * need in that case.
		 */

		iface->origKinds = mappingCreate (NULL);
		if (iface->origKinds == NULL)
			goto port_bad;

		if (mappingEnumerate (shul->kinds, recordOrigKindRep,
				      iface->origKinds) != NULL)
			goto port_bad;
	}

	iface->import = importing;

	/* The main work */

	ret = fileProcess (shul, fileItem, ".ghi", 
			   importing ? "import:" : "export",
			   importing ? importFindFunc : exportFindFunc,
			   &ctx);

	if (ret == 0 && ctx.paramIndex < iface->nparams) {
		fprintf (stderr,
			 "Excess import/export parameters provided "
			 "(had %d, used %d)\n",
			 iface->nparams, ctx.paramIndex);
		ret = -1;
	}

	if (ret == 0 && histAdd (shul, 
				 importing ? HT_IMPORT : HT_EXPORT,
				 iface) == 0) {
		mappingDelete (ctx.localSyms, localVarFree, NULL);
		identTableDelete (ctx.localTerms);
		identTableDelete (ctx.localKinds);

		if (!importing && ctx.exportFail)
			ret = -1; /* XXX but keep interface */

		return ret;
	}

port_bad:

	if (ctx.localTerms != NULL)
		identTableDelete (ctx.localTerms);

	if (ctx.localSyms != NULL)
		mappingDelete (ctx.localSyms, localVarFree, NULL);

	if (ctx.localKinds != NULL)
		identTableDelete (ctx.localKinds);

	ifaceFree (shul, iface);
	return -1;

}

static void
ifaceFree (SHULLIVAN * shul, INTERFACE * iface)
{
	MAP_ELEM * me;
	MAP_ELEM * nextme;
	IDENT * id;
	SYMBOL * sym;
	TERM * term;
	KIND * kind;

	if (iface->import) {
		/*
		 * Free any statements, terms, and kinds
		 * which came from the interface. It is assumed
		 * that any later work which depended upon these has
		 * been freed first.
		 */

		MAP_ELEM_ITER_SAFE (shul->syms, me, nextme) {
			sym = me->v.p;
			assert (sym != NULL);
			if ((sym->stype == ST_STMT || 
			     sym->stype == ST_DEFJUST) &&
			    ((STATEMENT *)sym)->iface == iface) {
				id = me->obj;
				(void)mapElemDelete (me->obj, shul->syms);
				statementFree ((STATEMENT *)sym);
			}
		}

		MAP_ELEM_ITER_SAFE (shul->terms, me, nextme) {
			term = me->v.p;
			assert (term != NULL);
			if (term->iface == iface) {
				id = me->obj;
				free (term); /* iface->terms gets cleaned up
						below */
				(void)mapElemDelete (me->obj, shul->terms);
				(void)identFree (id);
			}
		}

		MAP_ELEM_ITER_SAFE (shul->kinds, me, nextme) {
			kind = me->v.p;
			assert (kind != NULL);
			if (kind->iface == iface) {
				free (kind);
				id = me->obj;
				(void)mapElemDelete (me->obj, shul->kinds);
				(void)identFree (id);
			}
		}
	}

	if (iface->origKinds) {
		mappingEnumerate (iface->origKinds, restoreOrigKindRep, NULL);
		mappingDelete (iface->origKinds, NULL, NULL);
	}
	free (iface->prefix); /* OK for NULL */
	free (iface->params);
	if (iface->terms)
		identTableDelete (iface->terms);
	if (iface->kinds)
		identTableDelete (iface->kinds);
	if (iface->sym.ident) {
		(void)mapElemDelete (iface->sym.ident, shul->interfaces);
		(void)identFree (iface->sym.ident);
	}
	identFree (iface->fileId);
	free (iface);
}

typedef struct _STMT_FOR_IFACE_CTX {
	INTERFACE * iface;
	FILE * f;
} STMT_FOR_IFACE_CTX;

static void *
stmtForIface (void * ctx, MAP_ELEM * me)
{
	STMT_FOR_IFACE_CTX * c = ctx;
	STATEMENT * stmt = me->v.p;

	assert (stmt != NULL);

	if (stmt->iface == c->iface)
		statementPrint (c->f, stmt, 0);

	return NULL;
}

static void
ifacePrint (FILE * f, SHULLIVAN * shul, INTERFACE * iface, int verbose)
{
	INTERFACE * param;
	int i;
	char * tag;

	assert (iface != NULL);

	if (verbose & PRINT_AS_GHI) {
		verbose &= ~PRINT_AS_GHI;
		tag = "param";
	} else if (iface->import)
		tag = "import";
	else
		tag = "export";
			

	fprintf (f, "%s (%s %s (", 
		 tag,
		 iface->sym.ident->name,
		 iface->fileId->name);

	for (i = 0; i < iface->nparams; ++i) {
		param = iface->params[i];
		fprintf (f, " %s", param->sym.ident->name);
	}

	fprintf (f, " ) \"%s\")\n", iface->prefix ? iface->prefix : "");

	if (verbose == 0)
		return;

	fprintf (f, "   Kinds: ");

	(void)mappingEnumerate (iface->kinds, idPrint, f);

	fprintf (f, "\n   Terms: ");

	(void)mappingEnumerate (iface->terms, idPrint, f);

	if (iface->import) {
		STMT_FOR_IFACE_CTX c;

		c.iface = iface;
		c.f = f;

		fprintf (f, "\n   Statements: ");

		(void)mappingEnumerate (shul->syms, stmtForIface, &c);
	}

	printf ("\n");
}

static void *
kindClassCollect (void * ctx, MAP_ELEM * me)
{
	MAPPING * classes = ctx;
	MAPPING * class;
	MAP_ELEM * classme;
	KIND * kind = me->v.p;

	classme = mapElemInsert (kind->rep, classes);
	if (classme == NULL) {
		ALLOC_ERR ();
		return me; /* stop the walk */
	}
	class = classme->v.p;
	if (class == NULL) {
		/* new class */
		class = mappingCreate (NULL);
		if (class == NULL) {
			ALLOC_ERR ();
			return me;
		}
		classme->v.p = class;
	}

	if (mapElemInsert (kind, class) == NULL) {
		ALLOC_ERR ();
		return me;
	}
	return NULL;
}

static int
kindList (SHULLIVAN * shul, ITEM * ignored)
{
	MAPPING * classes;
	MAP_ELEM * me;
	MAP_ELEM * nextme;
	MAP_ELEM * me2;
	MAP_ELEM * nextme2;
	MAPPING * classMap;
	KIND * kind;

	if ((classes = mappingCreate(NULL)) == NULL) {
		ALLOC_ERR ();
		return -1;
	}
	(void)mappingEnumerate (shul->kinds, kindClassCollect, classes);

	MAP_ELEM_ITER_SAFE (classes, me, nextme) {
		if ((classMap = me->v.p) == NULL)
			continue;

		kind = me->obj;
		printf ("(");
		MAP_ELEM_ITER_SAFE (classMap, me2, nextme2) {
			kind = me2->obj;
			printf (" %s", kind->id->name);
		}
		printf (" )\n");
		mappingDelete (classMap, NULL, NULL);
	}
	mappingDelete (classes, NULL, NULL);
	return 0;
}

static void *
kindRawPrint (void * ctx, MAP_ELEM * me)
{
	KIND * kind = me->v.p;
	printf ("%s --> %s\n",
		(char *)me->obj, kind->rep->id->name);
	return NULL;
}

static int
kindsRaw (SHULLIVAN * shul, ITEM * ignored)
{
	(void)mappingEnumerate (shul->kinds, kindRawPrint, shul);
	return 0;
}

static int
interfaceList (SHULLIVAN * shul, ITEM * ignored)
{
	unsigned long i;
	HISTORY_ITEM * hi;

	for (i = 0; i < shul->histlen; ++i) {
		hi = &shul->history[i / HISTORY_CHUNK_SIZE]->
			h[i % HISTORY_CHUNK_SIZE];
		if (hi->htype == HT_IMPORT || hi->htype == HT_EXPORT)
			ifacePrint (stdout, shul, hi->it, 1);
	}
	return 0;
}

static void *
idNamePrint (void * ctx, MAP_ELEM * me)
{
	FILE * f = ctx;
	fprintf (f, " %s", (char *)me->obj);
	return NULL;
}

static int
identifierList (SHULLIVAN * shul, ITEM * ignored)
{
	(void)mappingEnumerate (allIdents, idNamePrint, stdout);
	printf ("\n");
	return 0;
}

static void
termPrint (FILE * f, TERM * term)
{
	int i;
	fprintf (f, "term (%s (%s", term->kind->id->name, 
		 term->sym.ident->name);
	for (i = 0; i < term->arity; ++i)
		fprintf (f, " %s", term->kinds[i]->id->name);
	fprintf (f, "))\n");
}

static void *
termPrintMe (void * ctx, MAP_ELEM * me)
{
	TERM * term = me->v.p;
	termPrint (stdout, term);
	return NULL;
}

static int
termList (SHULLIVAN * shul, ITEM * ignored)
{
	(void)mappingEnumerate (shul->terms, termPrintMe, shul);
	return 0;
}


static void
defPrint (FILE * f, DEF * def)
{
	int i;

	fprintf (f, "def ((%s", def->t.sym.ident->name);

	for (i = 0; i < def->t.arity; ++i) {
		fprintf (f, " %s", def->vi[i].id->name);
	}

	fprintf (f, ") ");

	exprPrint (f, def->expr, 0, 0);

	fprintf (f, ")\n");
}

static void *
defPrintMe (void * ctx, MAP_ELEM * me)
{
	DEF * def = me->v.p;

	if (def->t.sym.stype != ST_DEF)
		return NULL;

	defPrint (stdout, def);
	return NULL;
}

static int
defList (SHULLIVAN * shul, ITEM * ignored)
{
	(void)mappingEnumerate (shul->terms, defPrintMe, shul);
	return 0;
}

static void *
varForKind (void * ctx, MAP_ELEM * me)
{
	KIND * kind = ctx;
	SYMBOL * sym = me->v.p;
	VAR * var;

	if (sym->stype != ST_VAR)
		return NULL;

	var = SYM2VAR (sym);
	if (var->ex.kind != kind)
		return NULL;

	printf (" %s", var->sym.ident->name);
	return NULL;
}

static void *
varsForKindPrint (void * ctx, MAP_ELEM * me)
{
	SHULLIVAN * shul = ctx;
	KIND * kind = me->v.p;
	IDENT * id = me->obj;

	printf ("var (%s", id->name);
	(void)mappingEnumerate (shul->syms, varForKind, kind);
	printf (")\n");
	return NULL;
}

static int
varList (SHULLIVAN * shul, ITEM * ignored)
{
	(void)mappingEnumerate (shul->kinds, varsForKindPrint, shul);
	return 0;
}

static int
stats (SHULLIVAN * shul, ITEM * ignored)
{
	printf ("%lu history items\n", shul->histlen);
	printf ("%u symbols (stmt or var)\n", shul->syms->size);
	printf ("%u terms\n", shul->terms->size);
	printf ("%u kinds\n", shul->kinds->size);
	printf ("%u interfaces\n", shul->interfaces->size);
	printf ("%lu identifiers\n", numIdents);
	printf ("%lu mappings in use\n", mappings);
	printf ("MAP_ELEMs: total %lu, in use %lu, free %lu\n",
		numMapElems, numMapElems - freeMapElems, freeMapElems);
	printf ("VARs: total %lu, in use %lu, free %lu\n",
		var_alloc.n, var_alloc.n - var_alloc.nFree, 
		var_alloc.nFree);
	return 0;
}

static int
echo (SHULLIVAN * shul, ITEM * sexpr)
{
	assert (sexpr != NULL);
	sexpr_print (stdout, sexpr);
	printf ("\n");
	return 0;
}

static int
verbose (SHULLIVAN * shul, ITEM * sexpr)
{
	int verb;
	char * stop;

	assert (sexpr != NULL);
	if (sexpr->it.itype != IT_IDENT) {
		fprintf (stderr, "The argument to 'verbose' should "
			 "be a numeric value.\n");
		return -1;
	}
	verb = strtol (sexpr->id.id->name, &stop, 0);
	if (stop != sexpr->id.id->name)
		shul->verbose = verb;
	printf ("Verbosity is 0x%x.\n", shul->verbose);
	return 0;
}

static int
flags (SHULLIVAN * shul, ITEM * sexpr)
{
	unsigned long flg;
	char * stop;

	assert (sexpr != NULL);
	if (sexpr->it.itype != IT_IDENT) {
		fprintf (stderr, "The argument to 'flags' should "
			 "be a numeric value.\n");
		return -1;
	}
	flg = strtol (sexpr->id.id->name, &stop, 0);
	if (stop != sexpr->id.id->name) {
		/* REQ_MULT_CONC_SYNTAX implies MULTIPLE_CONCLUSIONS */
		if (flg & REQ_MULT_CONC_SYNTAX)
			flg |= MULTIPLE_CONCLUSIONS;
		shul->flags = flg;
	} else {
		flg = shul->flags;
		printf ("Current shullivan flags : 0x%lx\n", flg);
		printf ("0x%x : Allow statements with 0 or more "
			"conclusions [%s]\n", MULTIPLE_CONCLUSIONS,
			(flg & MULTIPLE_CONCLUSIONS) ? "On" : "Off");
		printf ("0x%x : Allow kind inference for variables in "
			"hypotheses or conclusions [%s]\n", LOOSE_VAR_KINDS,
			(flg & LOOSE_VAR_KINDS) ? "On" : "Off");
		printf ("0x%x : Allow variable kind inference in "
			"exported statements [%s]\n", EXPORT_LOOSE_VAR_KINDS,
			(flg & EXPORT_LOOSE_VAR_KINDS) ? "On" : "Off");
		printf ("0x%x : Print warnings about unneeded DV items in "
			"exported statements [%s]\n", EXPORT_WARN_DV,
			(flg & EXPORT_WARN_DV) ? "On" : "Off");
		printf ("0x%x : Require multiple conclusion syntax [%s]\n",
			REQ_MULT_CONC_SYNTAX, 
			(flg & REQ_MULT_CONC_SYNTAX) ? "On" : "Off");
		printf ("0x%x : Definitions with dummies require "
			"justification [%s]\n",
			DEF_JUSTIFY, 
			(flg & DEF_JUSTIFY) ? "On" : "Off");
	}
	return 0;
}


static int
histPrint (FILE * f, SHULLIVAN * shul, 
	   unsigned long start, unsigned long stop, int verbose)
{
	unsigned long i;
	HISTORY_ITEM * hi;
	VAR * var;
	KIND * kind = NULL;
	KIND * varkind = NULL;
	STATEMENT * stat;
	DEF * def;
	int indent;

	assert (shul != NULL && 
		start <= shul->histlen && stop <= shul->histlen);

	if (shul->flags & REQ_MULT_CONC_SYNTAX)
		verbose |= PRINT_MULT_CONC;

	for (i = start; i < stop; ++i) {
		hi = &shul->history[i / HISTORY_CHUNK_SIZE]->
			h[i % HISTORY_CHUNK_SIZE];
		indent = 0;
		if (verbose & PRINT_HISTNUM)
			indent = fprintf (f, "%lu. ", i);
		switch (hi->htype) {
		case HT_THM:
			stat = hi->it;
			if ((verbose & PRINT_ONLY_THM) && stat->thm == NULL)
				continue;
			statementPrint (f, hi->it, verbose | (indent << 16));
			break;
		case HT_EXPORT:
			if (verbose & PRINT_AS_GHI)
				continue;
			/* fall through */
		case HT_IMPORT:
			ifacePrint (f, shul, hi->it, verbose & PRINT_AS_GHI);
			break;
		case HT_VAROLDKIND:
			if ((verbose & PRINT_INTERNAL) == 0)
				continue;

			if (hi->it != NULL)
				fprintf (f, 
					 "# The following var used to be of "
					 "kind %s\n",
					 ((KIND *)hi->it)->id->name);
			else
				fprintf (f, "# The following var is new.\n");
			break;
		case HT_VARNEWKIND:
			assert (varkind == NULL);
			varkind = hi->it;
			if (verbose & PRINT_INTERNAL)
				fprintf (f, "# The following var is now of "
					 "kind %s\n", varkind->id->name);
			break;
		case HT_VAR:
			var = hi->it;
			assert (varkind != NULL);
			fprintf (f, "var (%s %s)\n",
				 varkind->id->name,
				 var->sym.ident->name);
			varkind = NULL;
			break;
		case HT_DEF:
			def = hi->it;
			if (verbose & PRINT_DEF_AS_TERM)
				termPrint (f, &def->t);
			else
				defPrint (f, def);
			break;
		case HT_KINDBIND0:
			assert (kind == NULL);
			kind = hi->it;
			if (verbose & PRINT_INTERNAL)
				fprintf (f, "# old kind %s\n", kind->id->name);
			break;
		case HT_KINDBIND:
			assert (kind != NULL);
			fprintf (f, "kindbind (%s %s)\n", kind->id->name,
				 ((KIND *)hi->it)->id->name);
			kind = NULL;
			break;
		}
	}
	return 0;
}

static int
history (SHULLIVAN * shul, ITEM * ignored)
{
	int verbose = (PRINT_HISTNUM | PRINT_INTERNAL | 
		       PRINT_AS_THM | ABBREV_PROOF);
	if (shul->verbose & SHUL_VERB_PRINT_PRETTY)
		verbose |= PRINT_PRETTY;
	return histPrint (stdout, shul, 0, shul->histlen, verbose);
}

static int
saveIt (SHULLIVAN * shul, ITEM * item, int verbose)
{
	ITEM * fileItem;
	ITEM * numItem;
	unsigned long start = 0;
	char * end;
	FILE * f;
	int ret;
	int ret2;

	if (item->it.itype != IT_SLIST || 
	    (fileItem = item->sl.first) == NULL ||
	    fileItem->it.itype != IT_IDENT) {
saveSyntax:
		fprintf (stderr,
			 "*** Expected '[i]save (FILENAME [START_HISTNUM])'\n");
		return -1;
	}
	if ((numItem = fileItem->it.next) != NULL) {
		if (numItem->it.itype != IT_IDENT)
			goto saveSyntax;
		start = strtoul (numItem->id.id->name, &end, 0);
		if (end == numItem->id.id->name)
			goto saveSyntax;

		if (start >= shul->histlen) {
			fprintf (stderr,
				 "*** There are only %lu history items.\n",
				 shul->histlen);
			return -1;
		}
	}

	if (strcmp (fileItem->id.id->name, ".") == 0)
		f = stdout;
	else
		f = fopen (fileItem->id.id->name, "w");
	if (f == NULL) {
		perror ("fopen");
		fprintf (stderr, "*** Cannot open '%s' for writing.\n",
			 fileItem->id.id->name);
		return -1;
	}
	ret = histPrint (f, shul, start, shul->histlen,	verbose);
	ret2 = 0;
	if (f != stdout)
		ret2 = fclose (f);
	if (ret != 0)
		perror ("fclose");
	return ret == 0 ? ret2 : ret;
}

static int
save (SHULLIVAN * shul, ITEM * item)
{
	int verbose = PRINT_ONLY_THM | PRINT_AS_THM;
	if (shul->verbose & SHUL_VERB_PRINT_PRETTY)
		verbose |= PRINT_PRETTY;
	return saveIt (shul, item, verbose);
}

static int
isave (SHULLIVAN * shul, ITEM * item)
{
	int verbose = PRINT_AS_GHI | PRINT_DEF_AS_TERM;
	if (shul->verbose & SHUL_VERB_PRINT_PRETTY)
		verbose |= PRINT_PRETTY;
	return saveIt (shul, item, verbose);
}

static int
undoLast (SHULLIVAN * shul)
{
	HISTORY_ITEM * hi;
	unsigned long i;
	VAR * var;
	KIND * kind;
	DEF * def;
	SYMBOL * sym;
	int j;

	i = shul->histlen;
	if (i == 0)
		return -1;

	--i;
	hi = &shul->history[i / HISTORY_CHUNK_SIZE]->
		h[i % HISTORY_CHUNK_SIZE];
	switch (hi->htype) {
	case HT_VAR:
		assert (i >= 2 && hi[-1].htype == HT_VARNEWKIND &&
			hi[-2].htype == HT_VAROLDKIND);
		var = hi->it;
		kind = hi[-2].it;
		if (kind != NULL)
			var->ex.kind = kind;
		else {
			mapElemDelete (var->sym.ident, shul->syms);
			identFree (var->sym.ident);
			varFree (var);
		}
		shul->histlen -= 3;
		break;

	case HT_IMPORT:
	case HT_EXPORT:
		ifaceFree (shul, hi->it); /* also removes ident from
					     shul->interfaces and frees it */
		shul->histlen --;
		break;

	case HT_THM:
		sym = hi->it;
		assert (sym->stype == ST_STMT);
		mapElemDelete (sym->ident, shul->syms);
		statementFree ((STATEMENT *)sym); /* also frees sym->ident */
		shul->histlen --;
		break;

	case HT_KINDBIND:
		assert (i >= 1 && hi[-1].htype == HT_KINDBIND0);
		kind = hi->it;
		mapElemDelete (kind->id, shul->kinds);
		identFree (kind->id);
		free (kind);
		shul->histlen -= 2;
		break;

	case HT_DEF:
		def = hi->it;
		mapElemDelete (def->t.sym.ident, shul->terms);
		identFree (def->t.sym.ident);
		for (j = 0; j < def->t.arity + def->ndummies; ++j)
			identFree (def->vi[j].id);
		free (def);
		shul->histlen --;
		break;

	case HT_KINDBIND0:
	case HT_VAROLDKIND:
	case HT_VARNEWKIND:
	default:
		assert (0);
	}
	return 0;
}

static int
undo (SHULLIVAN * shul, ITEM * unused)
{
	int ret = undoLast (shul);
	if (ret != 0)
		fprintf (stderr, "*** No history items left.");
	return ret;
}

static int
erase (SHULLIVAN * shul, ITEM * item)
{
	unsigned long i;
	char * end;

	if (item->it.itype != IT_IDENT) {
eraseSyntax:
		fprintf (stderr,
			 "*** Expected 'erase HISTORY_ITEM_NUMBER'\n");
		if (shul->histlen != 0)
			fprintf (stderr, "History item numbers : "
				 "0 <= n < %lu\n", shul->histlen);
		else
			fprintf (stderr, "There are no history items.\n");
		return -1;
	}
	i = strtoul (item->id.id->name, &end, 0);
	if (end == item->id.id->name)
		goto eraseSyntax;
	if (i >= shul->histlen)
		goto eraseSyntax;

	/* Note, undoLast() may erase a bit past i if HT_VAR* or HT_KINDBIND*
	 * items are involved.
	 */
	while (shul->histlen > i)
		undoLast (shul);

	return 0;
}

static EXPR *
exprParse3 (ITEM * item, EXPR_PARSE_CONTEXT * pctx, ARENA * arena)
{
	S_EXPR * sexpr;
	EXPR * exp;
	int i;
	TERM * term;
	ITEM * item2;
	SYMBOL * sym;
	VAR * var;
	MAP_ELEM * me;
	EXPR_VARINFO * vi;

	if (item->it.itype == IT_IDENT) {
		me = mapElemInsert (item->id.id, pctx->varIndex);
		if (me == NULL) {
			ALLOC_ERR ();
			return NULL;
		}
		if (me->v.p != NULL) {
			return (EXPR *)me->v.p;
		}
		sym = mapVal (item->id.id, pctx->syms);
		if (sym == NULL && sym->stype != ST_VAR) {
			fprintf (stderr, "*** Unknown variable '%s'\n",
				 item->id.id->name);
			/* varIndex will be cleaned up later */
			return NULL;
		}

		vi = arenaAlloc (arena, sizeof (*vi));
		if (vi == NULL) {
			ALLOC_ERR ();
			return NULL;
		}
		var = SYM2VAR (sym);

		vi->ex.etype = ET_IVAR;
		vi->ex.kind = var->ex.kind;
		vi->id = item->id.id;
		vi->index = pctx->varIndex->size - 1;
		me->v.p = vi;

		return (EXPR *)vi;
	}

	assert (item->it.itype == IT_SLIST);
	if ((item = item->sl.first) == NULL) {
		fprintf (stderr,
			 "*** Empty term S-expression.\n");
		return NULL;
	}
	if (item->it.itype != IT_IDENT) {
		fprintf (stderr,
			 "*** Expected term symbol, got "
			 "list\n");
		return NULL;
	}
	term = mapVal (item->id.id, pctx->terms);
	if (term == NULL) {
		fprintf (stderr,
			 "*** Unknown term symbol '%s'.\n",
			 item->id.id->name);
		return NULL;
	}
	sexpr = arenaAlloc (arena, (offsetof (S_EXPR, args) + 
				    term->arity * sizeof (EXPR *)));
	if (sexpr == NULL) {
		ALLOC_ERR ();
		return NULL;
	}

	sexpr->ex.etype = ET_SEXPR;
	sexpr->ex.kind = term->kind;
	sexpr->t = term;

	i = 0;
	for (item2 = item->it.next;
	     item2 != NULL;
	     item2 = item2->it.next) {
		if (i >= term->arity) {
			fprintf (stderr,
				 "*** Excess arguments to term '%s'.\n", 
				 term->sym.ident->name);
			return NULL;
		}
		exp = exprParse3 (item2, pctx, arena);
		if (exp == NULL)
			return NULL;

		if (exp->ex.kind->rep != term->kinds[i]->rep) {
			fprintf (stderr,
				 "*** Term argument kind mismatch: "
				 "wanted kind '%s', got '%s'\n",
				 term->kinds[i]->id->name, 
				 exp->ex.kind->id->name);
			return NULL;
		}
		sexpr->args[i++] = exp;
	}
	if (i < term->arity) {
		fprintf (stderr,
			 "*** Excess arguments to term '%s'.\n",
			 term->sym.ident->name);
		return NULL;
	}
	return (EXPR *)sexpr;
}

typedef struct _CHECK_CONC_CTX {
	ARENA * arena;
	VMAP * dvmap;
	int nvars;
	int nhvars;
} CHECK_CONC_CTX;

static int
checkConclusion (EXPR * pse, EXPR * scon, EXPR ** env, EXPR * deftgt,
		 CHECK_CONC_CTX * c)
{
	DEF * def;
	int i;
	int n;

	if (scon->ex.etype == ET_SEXPR) {
		if (pse->ex.etype == ET_SEXPR &&
		    pse->sx.t == scon->sx.t) {
			for (i = 0; i < scon->sx.t->arity; ++i) {
				if (checkConclusion (pse->sx.args[i],
						     scon->sx.args[i],
						     env, deftgt, c) != 0)
					return -1;
			}
			return 0;
		}
		if (scon->sx.t->sym.stype != ST_DEF) {
			fprintf (stderr,
				 "*** Term mismatch (wanted (%s ...)) in "
				 "conclusion.\n",
				 scon->sx.t->sym.ident->name);
			return -1;
		}
		def = (DEF *) scon->sx.t;
		/* when scon was constructed we checked that the actual
		   number of arguments matched scon->sx.t->arity */

		n = def->ndummies + def->t.arity;

		/*
		 * By putting this in tip->arena, we keep it around
		 * longer than we need to, but only until the end of the
		 * proof attempt.
		 *
		 * The +1 guards against a NULL return in the case
		 * n == 0.
		 */
		env = arenaAlloc (c->arena, n * sizeof (*env) + 1);
		if (env == NULL) {
			ALLOC_ERR ();
			return -1;
		}

		for (i = 0; i < def->t.arity; ++i)
			env[i] = scon->sx.args[i];

		for (; i < n; ++i)
			env[i] = NULL; /* space for dummies */

		/* note we set deftgt to pse: */

		return checkConclusion (pse, def->expr, env, pse, c);
	}

	assert (scon->ex.etype == ET_IVAR);

	if (env == NULL) {
		if (pse == scon) {
			/* Indicate that the variable was used in the
			   remnant. (EXPR *)c->dvmap is just used as
			   a non-NULL signature value which will not collide
			   with the address of any real expression. */

			if (pse->vi.index >= c->nhvars &&
			    c->dvmap[pse->vi.index - c->nhvars].ex == NULL)
				c->dvmap[pse->vi.index - c->nhvars].ex = 
					(EXPR *)c->dvmap;
			return 0;
		}

		fprintf (stderr,
			 "*** conclusion mismatch, expected variable '%s'\n",
			 scon->vi.id->name);
		return -1;
	}

	/* Since env is non-NULL, we are working on expanding a def,
	 * and all the variables we encounter are those occurring on the
	 * LHS or RHS of a def.
	 */

	if (env[scon->vi.index] != NULL)
		return checkConclusion (pse, env[scon->vi.index], NULL,
					NULL, c);

	/* OK, it's a definition dummy which hasn't been associated yet */

	if (pse->ex.etype == ET_SEXPR) {
		fprintf (stderr,
			 "*** Non-variable bound to definition dummy\n");
		return -1;
	}

	assert (pse->ex.etype == ET_IVAR);

	if (pse->vi.index < c->nvars) {
		fprintf (stderr,
			 "*** Variable '%s' from hypothesis or conclusion "
			 "bound to definition dummy\n",
			 pse->vi.id->name);
		return -1;
	}

	if (c->dvmap[pse->vi.index - c->nhvars].ex != NULL) {
		fprintf (stderr,
			 "*** Variable '%s' bound to two definition dummies\n",
			 pse->var.sym.ident->name);
		return -1;
	}

#if 0
	printf ("%s --> ", pse->vi.id->name);
	exprPrint (stdout, deftgt, 0, 0);
	printf ("\n");
#endif
	c->dvmap[pse->vi.index - c->nhvars].ex = deftgt;
	env[scon->vi.index] = pse;
	return 0;
}

static void
tipShow (FILE * f, TIP * tip, unsigned long verbose)
{
	int i;
	int indent;

	if (tip->ps.count == 0)
		fprintf (f, "Proof stack empty.\n");
	else {
		for (i = 0; i < tip->ps.count; ++i) {
			indent = fprintf (f, "PS%-3d ", i);
			exprPrint (f, tip->ps.exprs[i], verbose, indent);
			fprintf (f, "\n");
		}
	}
	if (tip->wvs.count == 0)
		fprintf (f, "WV stack empty.\n");
	else {
		for (i = 0; i < tip->wvs.count; ++i) {
			indent = fprintf (f, "WV%-3d ", i);
			exprPrint (f, tip->wvs.exprs[i], verbose, indent);
			fprintf (f, "\n");
		}
	}
}

static void
proofNbhdPrint (ITEM * stepItem, int step, int nSteps)
{
	int low;
	int high;
	int i;

	fprintf (stderr, "[%d] ", step);
	low = step;
	high = step + 1;

	/* printf a range of 5 steps containing the failed step */

	while (high - low < 5) {
		if (low > 0)
			--low;
		if (high < nSteps && high - low < 5)
			++high;
		if (low == 0 && high == nSteps)
			break;
	}

	if (low > 0)
		fprintf (stderr, "... ");

	for (i = 0; i < low; ++i)
		stepItem = stepItem->it.next;

	for (i = low; i < high; ++i) {
		if (i == step)
			fprintf (stderr, "** ");
		sexpr_print (stderr, stepItem);
		if (i == step)
			fprintf (stderr, " ** ");
		else
			fprintf (stderr, " ");
		stepItem = stepItem->it.next;
	}
	if (high < nSteps)
		fprintf (stderr, "...");
	fprintf (stderr, "\n");
}

static size_t
exprSize (EXPR * exp)
{
	size_t size;
	int i;
	if (exp->ex.etype == ET_SEXPR) {
		size = (offsetof (S_EXPR, args) + 
			exp->sx.t->arity * sizeof (EXPR *));

		size = ARENA_ROUND_UP (size);

		for (i = 0; i < exp->sx.t->arity; ++i)
			size += exprSize (exp->sx.args[i]);
		return size;
	}

	return 0; /* variable space is accounted for elsewhere */
}

static EXPR *
exprCopy (EXPR * exp, char ** ppMem, EXPR_VARINFO * vi, int nvars)
{
	int i;
	S_EXPR * sx;
	size_t size;

	if (exp->ex.etype == ET_SEXPR) {
		sx = (S_EXPR *) *ppMem;
		sx->ex = exp->sx.ex;
		sx->t = exp->sx.t;

		size = (offsetof (S_EXPR, args) + 
			exp->sx.t->arity * sizeof (EXPR *));

		size = ARENA_ROUND_UP (size);

		*ppMem += size;

		for (i = 0; i < exp->sx.t->arity; ++i)
			sx->args[i] = exprCopy (exp->sx.args[i], ppMem,
						vi, nvars);
		return (EXPR *)sx;
	}

	assert (exp->ex.etype == ET_IVAR);

	/* 
	 * Variables in the hypotheses or conclusions don't change
	 * location.
	 */

	if (exp->vi.index < nvars)
		return exp;

	/* Other variables occurring in the proof steps have moved. */
	return (EXPR *)(vi + (exp->vi.index - nvars));
}


static int
proofHold (THEOREM * thm, int allvars, VMAP * vmap, SHULLIVAN * shul)
{
	int i;
	PROOF_STEP * s;
	size_t size = sizeof (PROOF_STEP) * thm->nSteps;
	char * pMem;
	EXPR_VARINFO * vi;
	int nvars;

	for (i = 0; i < thm->nSteps; ++i) {
		s = &thm->steps[i];
		/* STEPT_HYP and STEPT_REF take up no additional space */
		if (s->s.type == STEPT_EXPR)
			size += exprSize (s->expr.x);
	}

	/*
	 * Space for the variables occurring in the proof steps but
	 * not in the hypotheses or conclusions.
	 */

	nvars = thm->stmt->nWild + thm->stmt->nhvars;

	size += sizeof (EXPR_VARINFO) * (allvars - nvars);

	s = malloc (size);
	if (s == NULL)
		return -1;

	pMem = (char *)s;
	pMem += sizeof (PROOF_STEP) * thm->nSteps;

	vmap += thm->stmt->nWild; /* skip over vMap entries corresponding to
				     wild variables */

	vi = (EXPR_VARINFO *)pMem; /* This is where the EXPR_VARINFO's for
				      variables in the proof steps but not in
				      the hypotheses or conclusions will be
				      finally put */

	for (i = 0; i < allvars - nvars; ++i) {
		*(EXPR_VARINFO *)pMem = *vmap [i].vi;
		/* all of these variables must correspond to global VARs,
		   we don't need to worry about ref counts */
		pMem += sizeof (EXPR_VARINFO);
	}
	for (i = 0; i < thm->nSteps; ++i) {
		s[i] = thm->steps[i]; /* copy the step itself */
		/* now copy any associated expressions */
		if (s[i].s.type == STEPT_EXPR)
			s[i].expr.x = exprCopy (s[i].expr.x, &pMem,
						vi, nvars);
	}
	thm->steps = s;
	thm->stmt->thm = thm;
	return 0;
}

typedef struct _LOAD_CONTEXT {
	IMPORT_CONTEXT ic; /* not all fields used */
	int interactive;
} LOAD_CONTEXT;

/*
 * Initialize *pTip, create a THEOREM, and check the proof steps.
 * When stat is NULL, this is a definition justification proof.
 */
static int
proof1 (SHULLIVAN * shul, STATEMENT_PARSE_CONTEXT * pSctx, TIP * pTip,
	STATEMENT * stat)
{
	IDENT * id;
	THEOREM * thm;
	ITEM * item;
	ITEM * hypItem;
	SYMBOL * sym;
	VAR * var;
	int i;
	PROOF_STEP * step;
	MAP_ELEM * me;
	EXPR * ex;
	EXPR_VARINFO * vi;
	int nvars;
	int djSeen = 0;

	thm = malloc (offsetof (THEOREM, hypnam) +
		      pSctx->hypnams->size * sizeof (IDENT *));

	if (thm == NULL) {
		perror ("proof1:malloc");
		goto proof1_bad1;
	}

	thm->stmt = stat;

	i = 0;
	for (item = pSctx->hypItem; item != NULL; item = item->it.next) {
		assert (item->it.itype == IT_SLIST);
		hypItem = item->sl.first;
		assert (hypItem != NULL && hypItem->it.itype == IT_IDENT);
		thm->hypnam[i++] = hypItem->id.id;

		/*
		 * hypItem->id.id->refcount has already been incremented
		 * when hypItem->id.id was added to pSctx->hypnams.
		 */
	}

	i = 0; /* quick count of proof steps */
	for (item = pSctx->proofStepItem; item != NULL;
	     item = item->it.next)
		++i;

	thm->nSteps = i;
	pTip->t = thm;
	pTip->step = 0;
	pTip->hypnams = pSctx->hypnams;
	pTip->varIndex = pSctx->ec.varIndex;

	nvars = pSctx->ec.varIndex->size;
	
	arenaInit (&pTip->arena, 0x10000, 0x2000000, &shul->backing);

	exprStackInit (&pTip->ps, &pTip->arena);	/* proof stack */
	exprStackInit (&pTip->wvs, &pTip->arena);	/* wild var. stack */

	if ((thm->steps = arenaAlloc (&pTip->arena,
				      i * sizeof (PROOF_STEP) + 1)) == NULL) {
		ALLOC_ERR ();
		goto proof1_bad2;
	}


	for (item = pSctx->proofStepItem; item != NULL;
	     item = item->it.next, ++pTip->step) {

		step = &thm->steps[pTip->step];
#if 0
		printf ("step %d: ", pTip->step);
		sexpr_print (stdout, item);
		printf ("\n");
#endif
		if (item->it.itype == IT_SLIST) {
			step->expr.s.type = STEPT_EXPR;
			step->expr.x = exprParse3 (item, &pSctx->ec, 
						   &pTip->arena);
			if (step->expr.x == NULL)
				goto proof1_bad3;
			
			goto checkstep;
		}

		assert (item->it.itype == IT_IDENT);

		id = item->id.id;

		/* first check for hypothesis name */
		i = mapValI (id, pTip->hypnams);
		if (i != -1) {
			step->hyp.s.type = STEPT_HYP;
			step->hyp.index = i;

			goto checkstep;
		}

		/* next check for a variable occurring in the
		   hypotheses or conclusions (or one already seen) */

		ex = mapVal (id, pTip->varIndex);
		if (ex != NULL) {
			step->expr.s.type = STEPT_EXPR;
			step->expr.x = ex;
			goto checkstep;
		}

		sym = mapVal (id, shul->syms);
		if (sym == NULL) {
			fprintf (stderr,
				 "*** Unknown proof step '%s'\n",
				 id->name);
			goto proof1_bad3;
		}

		if (sym->stype == ST_VAR) {

			me = mapElemInsert (id, pTip->varIndex);
			if (me == NULL) {
				ALLOC_ERR ();
				goto proof1_bad3;
			}

			assert (me->v.p == NULL);

			vi = arenaAlloc (&pTip->arena, sizeof (*vi));
			if (vi == NULL) {
				ALLOC_ERR ();
				goto proof1_bad3;
			}
			me->v.p = vi;

			/*
			 * Do not increment reference count on id,
			 * since both pTip->varIndex and the temporary variable
			 * vi will go away when we exit the caller.
			 */

			var = SYM2VAR (sym);

			vi->ex.etype = ET_IVAR;
			vi->ex.kind = var->ex.kind;
			vi->id = id;
			vi->index = pTip->varIndex->size - 1;
			step->expr.s.type = STEPT_EXPR;
			step->expr.x = (EXPR *)vi;
			goto checkstep;
		}

		if (sym->stype == ST_DEFJUST) {
			/*
			 * A definition justification step must occur only
			 * as the last step in a definition justification
			 * proof.
			 */
			if (stat != NULL) {
				fprintf (stderr,
					 "*** Definition justification rule "
					 "%s used in non-definition proof.\n",
					 id->name);
				goto proof1_bad3;
			}
			if (item->it.next != NULL) {
				fprintf (stderr,
					 "*** Definition justification rule "
					 "%s must be last step of proof.\n",
					 id->name);
				goto proof1_bad3;
			}
			djSeen = 1;
		} else
			assert (sym->stype == ST_STMT);

		step->ref.s.type = STEPT_REF;
		step->ref.stat = (STATEMENT *)sym;

checkstep:
		if (proofStepApply (shul, pTip, step) != 0) {
			if (step->ref.s.type == STEPT_REF) {
				int verbose = PRINT_VERBOSE;
				if (shul->verbose & 
				    SHUL_VERB_PRINT_PRETTY)
					verbose |= PRINT_PRETTY;
				fprintf (stderr, "*** Failed applying:\n");

				statementPrint (stderr, 
						step->ref.stat,
						verbose);
			}
			proofNbhdPrint (pSctx->proofStepItem,
					pTip->step, thm->nSteps);
			goto proof1_bad3;
		}
	}

	if ((stat == NULL) & !djSeen) {
		fprintf (stderr,
			 "A definition justification rule is needed as the "
			 "last step of proof.\n");
		goto proof1_bad3;
	}

	/*
	 * OK, now we must verify that the WV stack is empty, and
	 * what remains on the proof stack is just the conclusions
	 * of the theorem (if necessary expanding and checking any
	 * definitions occurring in the conclusions).
	 */

	if (pTip->wvs.count != 0) {
		fprintf (stderr,
			 "*** Wild variable stack must be empty "
			 "at end of proof.\n");
		goto proof1_bad3;
	}

	return 0;


proof1_bad3:

	memset (shul->dvbits, 0, shul->dvsize);

	tipShow (stderr, pTip, shul->verbose);

	arenaFree (&pTip->arena);

proof1_bad2:
	free (thm);
	pTip->t = NULL;

proof1_bad1:

	mappingEmpty (pSctx->ec.varIndex, NULL, NULL);
	/* caller must free stat */

	return -1;
}

static int
load_thm (SHULLIVAN * shul, ITEM * arg, void * ctx)
{
	STATEMENT * stat;
	STATEMENT_PARSE_CONTEXT sctx;
	THEOREM * thm;
	TIP tip;
	int i;
	MAP_ELEM * me;
	EXPR_VARINFO * vi;
	int nvars;
	int allvars;
	VMAP * vmap;
	DVC2 dv;
	CHECK_CONC_CTX checkCtx;
	int pairs;

	sctx.ec.terms = shul->terms;
	sctx.ec.syms = shul->syms;
	sctx.iface = NULL;
	if ((sctx.hypnams = mappingCreate (NULL)) == NULL) {
		ALLOC_ERR ();
		return -1;
	}

	sctx.hypnams->defval.i = -1;
	sctx.def_just = 0;

	stat = parseStatement (shul, arg, &sctx);
	if (stat == NULL)
		goto load_thm_bad0;  /* hypnams has been cleaned up for us */

	nvars = sctx.ec.varIndex->size;

	thm = NULL;
	/* Initialize tip, validate proof steps */
	if (proof1 (shul, &sctx, &tip, stat) != 0) {
		goto load_thm_bad2;
	}

	thm = tip.t;

	if (tip.ps.count != stat->nCons) {
		/*
		 * Hmm, we could be a bit more lenient, and just check that
		 * tip.ps.count >= stat->nCons...
		 */
		fprintf (stderr,
			 "*** Expected %d conclusions at end of proof, "
			 "have %d.\n", stat->nCons, tip.ps.count);
		goto load_thm_bad3;
	}


	/* 
	 * vmap will be an array mapping variable indices (offset by nvar)
	 * to a pair of the corresponding variable, and 
	 * - NULL, if the corresponding variable is not bound to a def dummy
	 * - the remnant subexpression matched against the def expansion
	 *   which caused the corresponding variable to be bound to a def
	 *   dummy.
	 */

	allvars = tip.varIndex->size;

	i = stat->nhvars;

	/*
	 * The +1 is so we don't get back NULL even if (allvars - i) == NULL.
	 */
	vmap = arenaAlloc (&tip.arena, (allvars - i) * sizeof (*vmap) + 1);
	if (vmap == NULL) {
		ALLOC_ERR ();
		goto load_thm_bad3;
	}

	/* 
	 * To initialize vmap, we iterate through varIndex, which we
	 * no longer need after this. An alternative would be to
	 * build up vmap earlier as we go through the proof steps, but we'd
	 * have to grow it dynamically. (Note that the EXPR_VARINFO's
	 * themselves cannot be moved, since they are referenced by
	 * various expressions in the proof.)
	 */

	while (NULL != (me = mapElemArb (tip.varIndex))) {
		vi = me->v.p;
		if (vi->index >= i) {
			vmap[vi->index - i].vi = vi;
			vmap[vi->index - i].ex = NULL;
		}
		mapElemDelete (me->obj, tip.varIndex);
	}


	/* 
	 * checkConclusion() matches the conclusions against the remnant
	 * expressions on the proof stack, expanding def's and checking
	 * binding of remnant variables against any definition dummy
	 * variables. It also collects in vmap info about the usage of
	 * variables in the remnant.
	 */

	checkCtx.arena = &tip.arena;
	checkCtx.nvars = nvars;
	checkCtx.nhvars = i; /* stat->nhvars */
	checkCtx.dvmap = vmap;

	for (i = 0; i < stat->nCons; ++i) {
		if (checkConclusion (tip.ps.exprs[i], stat->cons[i], 
				     NULL, NULL, &checkCtx) != 0)
			goto load_thm_bad3;
	}

	/*
	 * Check DV conditions for this statement.
	 * 1. Any DV pair required by the proof with both variables of the
	 *    pair in the hypotheses or conclusions, must occur in the DV
	 *    list for the theorem.
	 * 2. If a DV pair occurs involving a remnant variable bound to
	 *    a definition dummy, the other variable of the pair must belong
	 *    to the subexpression matched against the def expansion which
	 *    bound the def dummy to the first variable. Definition dummies
	 *    may be considered implicitly distinct, but only with respect
	 *    to other variables occurring in the (substituted) definition
	 *    RHS.
	 */

	dv.dvbits = stat->dvbits;
	dv.nvars = nvars;
	dv.nhvars = stat->nhvars;
	dv.missing = 0;
	dv.bad = 0;
	dv.vi = stat->vi;
	dv.vmap = vmap;

	if (dvEnumerate (allvars, shul->dvbits,
			 checkDvsForStat, &dv) != NULL)
		goto load_thm_bad3; /* shouldn't happen */
	
	if (dv.bad) {
		if (dv.missing)
			fprintf (stderr, ")\n");
		goto load_thm_bad3;
	}

	/* clear dvbits here when we know how many pairs we might have */

	pairs = allvars * (allvars - 1) / 2;
	memset (shul->dvbits, 0, BIT_MAP_SIZE(pairs));

	me = mapElemInsert (stat->sym.ident, shul->syms);
	if (me == NULL) {
		ALLOC_ERR ();
		goto load_thm_bad3;
	}
	/*
	 * parseStatement() checked that there was no existing
	 * statement of the same name.
	 */
	assert (me->v.p == NULL);

	me->v.p = stat;
	/* parseStatement() incremented stat->sym.ident->refcount */

	if (histAdd (shul, HT_THM, stat) != 0)
		goto load_thm_bad4;

	if (shul->saveProof) {
		if (proofHold (thm, allvars, vmap, shul) != 0) {
			fprintf (stderr, "Warning: cannot keep proof.\n");
			goto dropProof;
		}
	} else {
dropProof:
		/* Here we don't hold on to the THEOREM, just the STATEMENT. */
		for (i = 0; i < thm->stmt->nHyps; ++i)
			identFree (thm->hypnam[i]);
		free (thm);
	}

	arenaFree (&tip.arena);

	mappingEmpty (sctx.ec.varIndex, NULL, NULL);
	mappingDelete (sctx.hypnams, NULL, NULL);

	return 0;

load_thm_bad4:
	mapElemDelete (me->obj, shul->syms);
	stat->sym.ident->refcount--;

load_thm_bad3:

	memset (shul->dvbits, 0, shul->dvsize);

	tipShow (stderr, &tip, shul->verbose);

	arenaFree (&tip.arena);

	free (thm);

	mappingEmpty (sctx.ec.varIndex, NULL, NULL);

load_thm_bad2:
	statementFree (stat);

load_thm_bad0:
	if (sctx.hypnams != NULL)
		identTableDelete (sctx.hypnams);

	if (!((LOAD_CONTEXT *)ctx)->interactive &&
	    (shul->verbose & SHUL_VERB_COMMANDS) == 0) {
		fprintf (stderr, "thm ");
		sexpr_print (stderr, arg);
		fprintf (stderr, "\n");
	}
	return -1;
}

static int
load_var (SHULLIVAN * shul, ITEM * arg, void * ctx)
{
	LOAD_CONTEXT * lc = ctx;
	lc->ic.keephist = 1;
	
	return import_var (shul, arg, &lc->ic);
}

typedef struct _INT_PAIR
{
	int i1, i2;
} INT_PAIR;

static int
djParse (ITEM * rhsItem, EXPR * e1, EXPR * e2, 
	 TIP * tip, int nvars, int dummies, MAPPING * dmap, MAPPING * rmap)
{
	MAP_ELEM * me;
	MAP_ELEM * me1;
	MAP_ELEM * me2;
	EXPR * ex;
	int ix;
	int i1, i2;
	INT_PAIR * pair;

	if (rhsItem->it.itype == IT_SLIST) {
		rhsItem = rhsItem->sl.first;
		assert (rhsItem != NULL && rhsItem->it.itype == IT_IDENT);
		if (e1->ex.etype != ET_SEXPR || e2->ex.etype != ET_SEXPR ||
		    e1->sx.t->sym.ident != rhsItem->id.id ||
		    e2->sx.t->sym.ident != rhsItem->id.id)
			return -1;
		/*
		 * rhsItem, e1, and e2 have all been previously parsed/checked
		 * so we know they have the same arity, kinds, etc.
		 */

		for (ix = 0, rhsItem = rhsItem->it.next; 
		     rhsItem != NULL;
		     rhsItem = rhsItem->it.next, ++ix) {
			if (djParse (rhsItem, e1->sx.args[ix], e2->sx.args[ix],
				     tip, nvars, dummies, dmap, rmap) != 0)
				return -1;
		}
		return 0;
		
	} else {
		assert (rhsItem->it.itype == IT_IDENT);
		if (e1->ex.etype != ET_IVAR || e2->ex.etype != ET_IVAR)
			return -1;

		ex = mapVal (rhsItem->id.id, tip->varIndex);
		assert (ex != NULL && ex->ex.etype == ET_IVAR);
		ix = ex->vi.index;
		i1 = e1->vi.index;
		i2 = e2->vi.index;
		if (ix < nvars - dummies) {
			/* A non-dummy variable */
			if (i1 != ix || i2 != ix)
				return -1;
			return 0;
		}
		/* OK, ex is a dummy, e1 and e2 can't be non-dummies,
		 * and can't be equal.
		 */
		if (i1 < nvars - dummies || i2 < nvars - dummies || i1 == i2)
			return -1;
		me = mapElemInsert ((void *)(size_t)ix, dmap);
		if (me == NULL) {
			ALLOC_ERR();
			return -1;
		}
		if (me->v.p == NULL) {
			pair = arenaAlloc (&tip->arena, sizeof (*pair));
			if (pair == NULL) {
				ALLOC_ERR();
				return -1;
			}
			pair->i1 = i1;
			pair->i2 = i2;
			me->v.p = pair;
			me1 = mapElemInsert ((void *)(size_t)i1, rmap);
			if (me1 == NULL) {
				ALLOC_ERR();
				return -1;
			}
			me2 = mapElemInsert ((void *)(size_t)i2, rmap);
			if (me2 == NULL) {
				ALLOC_ERR();
				return -1;
			}
			if (me1->v.p != NULL || me2->v.p != NULL) {
				fprintf (stderr,
					 "*** Reused dummy variable\n");
				return -1;
			}
			me1->v.p = pair;
			me2->v.p = pair;
			return 0;
		}
		pair = me->v.p;
		if (pair->i1 != i1 || pair->i2 != i2)
			return -1;
		return 0;
	}
}

typedef struct _DEFDV
{
	int nondummies;
	MAPPING * rmap;
	int i, j;       /* failure case */
} DEFDV;

static void *
checkDvsForDef (int i, int j, void * ctx)
{
	DEFDV * dv = ctx;
	INT_PAIR * pairi;
	INT_PAIR * pairj;

	/* Note, i < j */
	if (j < dv->nondummies) {
		fprintf (stderr,
			 "*** DV condition involves two non-dummies in "
			 "definition justification proof:");
		goto checkDvsForDef_bad;
	}

	pairj = mapVal ((void *)(size_t)j, dv->rmap);
	if (pairj == NULL)
		return NULL; /* OK, j is neither def-dummy nor a def arg.
				No restrictions on its DV conditions. */

	pairi = mapVal ((void *)(size_t)i, dv->rmap);
	if (pairi == NULL)
		return NULL; /* OK, i is not a def-dummy, and j is a def-dummy.
				(i j) is an allowed DV condition. */

	/* Both i and j were definition dummies in one of the RHS variants.
	 * They must be in the same RHS variant.
	 */
	if ((i == pairi->i1 && j == pairj->i1) ||
	    (i == pairi->i2 && j == pairj->i2))
		return NULL;	/* i, j belong to the same RHS variant */

	fprintf (stderr, "*** DV condition involves two dummies in different\n"
		         "    definition RHS variants:");

checkDvsForDef_bad:
	dv->i = i; /* record failure case */
	dv->j = j;
	return dv; /* arbitrary non-NULL */
}

static int
defJustVerify (SHULLIVAN * shul, STATEMENT_PARSE_CONTEXT * sctx, TIP * tip,
	       ITEM * rhsItem, int nvars, int dummies)
{
	MAPPING * dmap;
	MAPPING * rmap;
	DEFDV dv;
	int result;

	if (tip->ps.count != 2) {
		fprintf (stderr, 
			 "Excess expressions on proof stack.\n");
		tipShow (stderr, tip, shul->verbose);
		return -1;
	}
	dmap = mappingCreate (NULL);
	if (dmap == NULL) {
		ALLOC_ERR();
		return -1;
	}
	rmap = mappingCreate (NULL);
	if (rmap == NULL) {
		ALLOC_ERR();
		result = -1;
		goto defJustVerify_bad1;
	}
	result = djParse (rhsItem, tip->ps.exprs[0], tip->ps.exprs[1],
			  tip, nvars, dummies, dmap, rmap);
	if (result != 0) {
		fprintf (stderr, 
			 "In definition justification proof, def_just "
			 "variables not substituted properly.\n");
		goto defJustVerify_bad2;
	}

	/*
	 * OK, at this point, if result == 0, we know that both RHS
	 * variants do in fact match the prototype RHS, and that completely
	 * different sets of definition dummies are used on the two sides.
	 * Now check the distinct variables requirements imposed by the proof.
	 */

	dv.nondummies = nvars - dummies;
	dv.rmap = rmap;

	result = 0;
	if (dvEnumerate (tip->varIndex->size, shul->dvbits,
			 checkDvsForDef, &dv) != NULL) {
		/* Disallowed DV pair occurred. Print out the pair. */
		fprintf (stderr, " (%s %s)\n",
			 sctx->ec.vars[dv.i].id->name,
			 sctx->ec.vars[dv.j].id->name);
		result = -1;
	}

defJustVerify_bad2:
	mappingDelete (rmap, NULL, NULL);

defJustVerify_bad1:
	mappingDelete (dmap, NULL, NULL);
	return result;
}

static int
load_def (SHULLIVAN * shul, ITEM * arg, void * ctx)
{
	ITEM * lhsItem;
	ITEM * rhsItem;
	ITEM * nameItem;
	ITEM * proofItem;
	ITEM * item;
	DEF * def;
	IDENT * id;
	MAP_ELEM * me;
	int arity;
	int dummies;
	int nvars;
	STATEMENT_PARSE_CONTEXT sctx;
	EXPR_PARSE_CONTEXT * parseCtx = &sctx.ec;
	TIP tip;
	size_t size;
	int i;

	if (arg->it.itype != IT_SLIST ||
	    (lhsItem = arg->sl.first) == NULL ||
	    lhsItem->it.itype != IT_SLIST ||
	    (nameItem = lhsItem->sl.first) == NULL ||
	    nameItem->it.itype != IT_IDENT ||
	    (rhsItem = lhsItem->it.next) == NULL) {
		fprintf (stderr, "*** Expected "
			 "'def ((NAME [VAR ...]) RHS [(STEP ...)])'\n");
		return -1;
	}

	id = nameItem->id.id;
	if (mapVal (id, shul->terms) != NULL) {
		fprintf (stderr, "'%s' already exists as a term "
			 "or definition symbol.\n", id->name);
		return -1;
	}

	/* we'll set me->v.p after we count the variables */

	parseCtx->terms = shul->terms;
	parseCtx->syms = shul->syms;

	exprParseCtxInit (parseCtx, shul);

	arity = 0;
	for (item = nameItem->it.next; 
	     item != NULL; item = item->it.next) {
		if (item->it.itype != IT_IDENT) {
			fprintf (stderr,
				 "*** formal parameter must be a "
				 "variable identifier.\n");
			goto load_def_bad1;
		}
		if (arity >= parseCtx->varsSize &&
		    growParseVars (parseCtx) != 0) {
			goto load_def_bad1;
		}
		me = mapElemInsert (item->id.id,
				    parseCtx->varIndex);
		if (me == NULL) {
			ALLOC_ERR ();
			goto load_def_bad1;
		}
		if (me->v.i != -1) {
			fprintf (stderr,
				 "*** duplicate formal definition "
				 "parameter '%s'.\n", (char *)me->obj);
			goto load_def_bad1;
		}
		parseCtx->vars[arity].index = arity;
		parseCtx->vars[arity].id = item->id.id;
		parseCtx->vars[arity].ex.etype = ET_IVAR;
		parseCtx->vars[arity].ex.kind = NULL;
		me->v.i = arity++;
	}

	if (exprParse1 (rhsItem, parseCtx, NULL) != 0) {
		fprintf (stderr,
			 "*** bad definition RHS.\n");
		goto load_def_bad1;
	}

	nvars = parseCtx->varIndex->size;
	dummies = nvars - arity;

	if (varDefaultKinds (parseCtx->vars, nvars,
			     (shul->flags & LOOSE_VAR_KINDS),
			     shul->syms) != 0)
		goto load_def_bad1;

	proofItem = rhsItem->it.next;
	if ((shul->flags & DEF_JUSTIFY) != 0) {
		if (proofItem != NULL) {
			if (dummies == 0) {
				fprintf (stderr, 
					 "*** Definition %s has no dummy "
					 "vars, justification proof must be "
					 "absent.\n",
					 nameItem->id.id->name);
				goto load_def_bad1;
			}
			if (proofItem->it.itype != IT_SLIST ||
			    proofItem->it.next != NULL) {
				fprintf (stderr, 
					 "*** Expected 'def ((NAME [VAR ...]) "
					 "RHS CONC (STEP ...))'\n");
				goto load_def_bad1;
			}
		} else if (dummies != 0) {
			fprintf (stderr, "*** Definition %s has dummy vars, "
				 "justification proof is required.\n",
				 nameItem->id.id->name);
			goto load_def_bad1;
		}
	} else if (proofItem != NULL) {
		fprintf (stderr, "*** Expected "
			 "'def ((NAME [VAR ...]) RHS)'\n");
		goto load_def_bad1;
	}


	/*
	 * OK, now we know all the parameter variables and dummies
	 * and their kinds, as well as enough information to size
	 * the RHS expression.  The nVarExps variable expressions
	 * are handled by the nvars EXPR_VARINFO's (note nvars <= nVarExps).
	 */

	size = (offsetof (DEF, vi) + 
		nvars * sizeof (EXPR_VARINFO) +
		((parseCtx->nTermExps + parseCtx->nDefExps)
		 * offsetof (S_EXPR, args)) +
		(parseCtx->nTermExps + parseCtx->nDefExps +
		 parseCtx->nVarExps - 1) * sizeof (EXPR *) +
		arity * sizeof (KIND *));

	def = malloc (size);
	if (def == NULL) {
		perror ("load_def:malloc");
		goto load_def_bad1;
	}

	def->t.sym.stype = ST_DEF;
	def->t.sym.ident = id;
	def->t.iface = NULL;
	def->t.kind = NULL; /* This will come from exprParse2() */
	def->t.arity = arity;

	def->ndummies = dummies;

	for (i = 0; i < nvars; ++i) {
		def->vi[i] = parseCtx->vars[i];
		def->vi[i].id->refcount++; /* hang on to it */
	}

	parseCtx->varIndex->defval.p = NULL;
	(void)mappingEnumerate (parseCtx->varIndex, varIndexRemap, def->vi);

	def->t.kinds = (KIND **)&def->vi[nvars];

	for (i = 0; i < arity; ++i) {
		def->t.kinds[i] = def->vi[i].ex.kind; /* redundant... */
	}

	parseCtx->pMem = (char *)&def->t.kinds[arity];

	def->expr = exprParse2 (rhsItem, parseCtx);
	assert (def->expr != NULL && def->expr->ex.kind != NULL &&
		parseCtx->pMem == (char *)def + size);

	def->t.kind = def->expr->ex.kind; /* redundant... */

	if (proofItem != NULL) {
		int pairs;
		int allvars;

		printf ("checking justification for definition of %s\n",
			nameItem->id.id->name);
		/* check definition justification proof */

		sctx.iface = NULL;
		/* Create an empty hypothesis list */
		if ((sctx.hypnams = mappingCreate (NULL)) == NULL) {
			ALLOC_ERR ();
			goto load_def_bad2;
		}
		sctx.hypnams->defval.i = -1;
		sctx.proofStepItem = proofItem->sl.first;
		sctx.hypItem = NULL; /* no hypotheses */

		i = proof1 (shul, &sctx, &tip, NULL);
		identTableDelete (sctx.hypnams); /* not needed any more */

		/* proof1() checked that the last step of the proof
		 * was a definition justification step.  Check that
		 * exactly 2 items remain on the proof stack, which
		 * must be the the two RHS versions.  Check that the
		 * two expressions do in fact match the RHS; we require
		 * that non-dummy variables match exactly, while
		 * dummies may differ; and a completely different
		 * dummy variable set must be used for each RHS.
		 * Then check the distinct variables requirements
		 * generated in the proof.  DV conditions are allowed
		 * between def dummies and non dummies, or between
		 * def dummies and other def dummies in the same
		 * RHS variant, or between any variable and an ordinary
		 * proof dummy that does not occur in one of the RHSs.
		 * DV pairs are not allowed between two non-dummy vars,
		 * or between def dummies occurring in different RHSs.
		 */

		if (i == 0)
			i = defJustVerify (shul, &sctx, &tip,
					   rhsItem, nvars, dummies);

		/* clear dvbits here when we know how many pairs we might
		   have */

		allvars = sctx.ec.varIndex->size;
		pairs = allvars * (allvars - 1) / 2;
		memset (shul->dvbits, 0, BIT_MAP_SIZE(pairs));

		if (i != 0)
			goto load_def_bad2;
	}

	me = mapElemInsert (id, shul->terms);
	if (me == NULL) {
		ALLOC_ERR ();
		goto load_def_bad2;
	}
	assert (me->v.p == NULL); /* we checked above */

	me->v.p = def;

	if (histAdd (shul, HT_DEF, def) != 0)
		goto load_def_bad3;

	id->refcount++; /* the definition identifier */

	mappingEmpty (parseCtx->varIndex, NULL, NULL);

	return 0;

load_def_bad3:
	mapElemDelete (id, shul->terms);

load_def_bad2:
	for (i = 0; i < def->t.arity + def->ndummies; ++i) {
		def->vi[i].id->refcount--; /* release */
	}
	free (def);

load_def_bad1:
	mappingEmpty (parseCtx->varIndex, NULL, NULL);

	return -1;
	
}

static int
load_import (SHULLIVAN * shul, ITEM * arg, void * ctx)
{
	return port (shul, arg, 1 /* importing */);
}

static int
load_export (SHULLIVAN * shul, ITEM * arg, void * ctx)
{
	LOAD_CONTEXT * lc = ctx;
	int ret = port (shul, arg, 0 /* exporting */);
	if (ret != 0)
		lc->ic.exportFail = 1;
	return 0; /* allow load to continue even if export fails... */
}

/* In a .gh load, kindbind adds an alias to an existing kind */

static int
load_kindbind (SHULLIVAN * shul, ITEM * arg, void * ctx)
{
	ITEM * k1Item;
	ITEM * k2Item;
	KIND * k1;
	KIND * k2;
	MAP_ELEM * me;

	if (arg->it.itype != IT_SLIST ||
	    (k1Item = arg->sl.first) == NULL ||
	    k1Item->it.itype != IT_IDENT ||
	    (k2Item = k1Item->it.next) == NULL ||
	    k2Item->it.itype != IT_IDENT ||
	    k2Item->it.next != NULL) {
		fprintf (stderr,
			 "*** 'kindbind' expects (kind1 kind2)\n");
		return -1;
	}

	assert (k1Item->id.id != NULL && k2Item->id.id != NULL);

	if ((k1 = mapVal (k1Item->id.id, shul->kinds)) == NULL) {

		fprintf (stderr,
			 "*** kind '%s' not known.\n",
			 k1Item->id.id->name);
		return -1;

	}

	k2 = malloc (sizeof (*k2));
	if (k2 == NULL) {
		perror ("load_kindbind:malloc");
		return -1;
	}
	
	k2->id = k2Item->id.id;
	k2->iface = NULL;
	k2->rep = k1;

	me = mapElemInsert (k2Item->id.id, shul->kinds);
	if (me == NULL) {
		ALLOC_ERR ();
		goto load_kindbind_bad1;
	}
	if (me->v.p != NULL) {
		fprintf (stderr,
			 "*** kind '%s' already exists.\n",
			 k2->id->name);
		goto load_kindbind_bad1;
	}
	me->v.p = k2;

	/*
	 * We record the type bound to in a separate history item
	 * in case the rep is changed by a subsequent kindbind done
	 * in an import.
	 */

	if (histAdd (shul, HT_KINDBIND0, k1) != 0)
		goto load_kindbind_bad2;
	if (histAdd (shul, HT_KINDBIND, k2) != 0) {
		shul->histlen --;
		goto load_kindbind_bad2;
	}

	k2Item->id.id->refcount++;

	return 0;

load_kindbind_bad2:
	mapElemDelete (me->obj, shul->kinds);
load_kindbind_bad1:
	free (k2);
	return -1;
}

static CMD_FUNC
loadFindCmd (char * cmd)
{
	int cmp;
	cmp = strcmp (cmd, "thm");
	if (cmp == 0)
		return load_thm;

	if (cmp < 0) {
		if (strcmp (cmd, "def") == 0)
			return load_def;
		if (strcmp (cmd, "import") == 0)
			return load_import;
		if (strcmp (cmd, "kindbind") == 0)
			return load_kindbind;
		if (strcmp (cmd, "export") == 0)
			return load_export;
	} else if (strcmp (cmd, "var") == 0)
		return load_var;

	return NULL;
}

static int
load (SHULLIVAN * shul, ITEM * fileItem)
{
	int res;
	LOAD_CONTEXT ctx;

	ctx.ic.iface = NULL;
	ctx.ic.localSyms = shul->syms;
	ctx.ic.localKinds = shul->kinds;
	ctx.ic.exportFail = 0;
	ctx.interactive = 0;

	assert (shul != NULL && fileItem != NULL);

	if (fileItem->it.itype != IT_IDENT) {
		fprintf (stderr, "*** Expected 'load FILEID\n");
		return -1;
	}

	res = fileProcess (shul, fileItem, ".gh", "load:",
			   loadFindCmd, &ctx);
	if (res != 0) {
		/* Back out partial changes */
		fprintf (stderr, "load failed.\n");
	}
	return res;
}

static int
changeDir (SHULLIVAN * shul, ITEM * dirItem)
{
	assert (shul != NULL && dirItem != NULL);

	if (dirItem->it.itype != IT_IDENT) {
		fprintf (stderr, "*** Expected 'cd DIRECTORY'\n");
		return -1;
	}
	if (chdir (dirItem->id.id->name) != 0) {
		perror ("chdir");
		return -1;
	}
	return 0;
}

static int
sysCommand (SHULLIVAN * shul, ITEM * cmdItem)
{
	char * cmd;
	int ret;

	assert (shul != NULL && cmdItem != NULL);

	if (cmdItem->it.itype != IT_IDENT) {
		fprintf (stderr, "*** Expected '! SHELL_COMMAND'\n");
		return -1;
	}

	cmd = cmdItem->id.id->name; /* UGH */

	ret = system (cmd);
	if (ret == -1) {
		perror ("system");
		return -1;
	}
	if (WIFEXITED (ret))
		ret = WEXITSTATUS(ret);
	else
		ret = -1; /* signalled, etc. */
	return ret;
}

static int
thm (SHULLIVAN * shul, ITEM * arg)
{
	LOAD_CONTEXT ctx;
	int res;
	int oldSaveProof = shul->saveProof;

	shul->saveProof = 1; /* always save interactive proofs */

	ctx.ic.iface = NULL;
	ctx.ic.localSyms = shul->syms;
	ctx.ic.localKinds = shul->kinds;
	ctx.interactive = 1;

	res =  load_thm (shul, arg, &ctx);
	shul->saveProof = oldSaveProof;
	return res;
}

static int
var (SHULLIVAN * shul, ITEM * arg)
{
	LOAD_CONTEXT ctx;

	ctx.ic.iface = NULL;
	ctx.ic.localSyms = shul->syms;
	ctx.ic.localKinds = shul->kinds;
	ctx.interactive = 1;

	return load_var (shul, arg, &ctx);
}

static int
kindbind (SHULLIVAN * shul, ITEM * arg)
{
	LOAD_CONTEXT ctx;

	ctx.ic.iface = NULL;
	ctx.ic.localSyms = shul->syms;
	ctx.ic.localKinds = shul->kinds;
	ctx.interactive = 1;

	return load_kindbind (shul, arg, &ctx);
}

static int
def (SHULLIVAN * shul, ITEM * arg)
{
	LOAD_CONTEXT ctx;

	ctx.ic.iface = NULL;
	ctx.ic.localSyms = shul->syms;
	ctx.ic.localKinds = shul->kinds;
	ctx.interactive = 1;

	return load_def (shul, arg, &ctx);
}

static int
saveProofToggle (SHULLIVAN * shul, ITEM * arg)
{
	shul->saveProof = !shul->saveProof;
	printf ("Proofs will be %s.\n", 
		shul->saveProof ? "kept" : "discarded");
	return 0;
}



#define CMD_OPT_SEXPR	1

static COMMAND_FUNC
commandLookup (char * cmd, int cmdlen, int * pOpts)
{
	*pOpts = CMD_OPT_SEXPR; /* default */
	if (strcmp (cmd, "cd") == 0) {
		return changeDir;
	}
	if (strcmp (cmd, "def") == 0) {
		return def;
	}
	if (strcmp (cmd, "echo") == 0) {
		return echo;
	}
	if (strcmp (cmd, "erase") == 0) {
		return erase;
	}
	if (strcmp (cmd, "export") == 0) {
		return export;
	}
	if (strcmp (cmd, "flags") == 0) {
		return flags;
	}
	if (strcmp (cmd, "import") == 0) {
		return import;
	}
	if (strcmp (cmd, "isave") == 0) {
		return isave;
	}
	if (strcmp (cmd, "kindbind") == 0) {
		return kindbind;
	}
	if (strcmp (cmd, "load") == 0) {
		return load;
	}
	if (strcmp (cmd, "save") == 0) {
		return save;
	}
	if (strcmp (cmd, "thm") == 0) {
		return thm;
	}
	if (strcmp (cmd, "var") == 0) {
		return var;
	}
	if (strcmp (cmd, "verbose") == 0) {
		return verbose;
	}
	if (strcmp (cmd, "!") == 0) {
		return sysCommand;
	}
	*pOpts = 0;
	if (strcmp (cmd, "defs") == 0) {
		return defList;
	}
	if (strcmp (cmd, "history") == 0) {
		return history;
	}
	if (strcmp (cmd, "kinds") == 0) {
		return kindList;
	}
	if (strcmp (cmd, "kindsraw") == 0) {
		return kindsRaw;
	}
	if (strcmp (cmd, "identifiers") == 0) {
		return identifierList;
	}
	if (strcmp (cmd, "interfaces") == 0) {
		return interfaceList;
	}
	if (strcmp (cmd, "keep") == 0) {
		return saveProofToggle;
	}
	if (strcmp (cmd, "statements") == 0) {
		return statementList;
	}
	if (strcmp (cmd, "terms") == 0) {
		return termList;
	}
	if (strcmp (cmd, "undo") == 0) {
		return undo;
	}
	if (strcmp (cmd, "variables") == 0) {
		return varList;
	}
	if (strcmp (cmd, "stats") == 0) {
		return stats;
	}
	return NULL;
}

static int
readlinePromptSet (SCANNER * scan, char * prompt)
{
	scan->ctx = prompt;
	return 1; /* we maintain a reference to prompt */
}

static int
command (SHULLIVAN * shul, SCANNER * scan)
{
	char * cmd;
	int res;
	ITEM * item;
	int opts;
	COMMAND_FUNC cmdFunc;

	if (scan->prompt_set)
		scan->prompt_set (scan, shulPrompt);

	res = scan->get_token (scan);
	cmd = scan->gb.buf;

	if (res == SCAN_ERR) {
		perror ("get_token returned SCAN_ERR");
		return COMMAND_ERR;
	}

	if (res == SCAN_EOF)
		return COMMAND_EOF;

	if (strcmp (cmd, "exit") == 0) {
		printf ("Cheerio!\n");
		return COMMAND_EOF;
	}

	if (strcmp (cmd, "help") == 0) {
		printHelp ();
		return COMMAND_CONTINUE_GOOD;
	}

	if (scan->prompt_set)
		scan->prompt_set (scan, shulContinuePrompt);

	if (res == SCAN_LPAREN) {
		printf ("Oops, expected a command and got '('\n"
			"Ignoring until matching ')'...\n");
		for (;;) {
			item = read_sexpr (shul, scan);
			if (item == NULL)
				return COMMAND_CONTINUE_BAD;
			sexpr_free (shul, item);
		}
	}

	if (res == SCAN_RPAREN) {
		printf ("Oops, expected a command and got ')'\n");
		return COMMAND_CONTINUE_BAD;
	}

	if ((cmdFunc = commandLookup (cmd, scan->idlen, &opts)) == NULL)
	{
		printf ("Unknown command '%s'. Type 'help' for help.\n",
			cmd);
		return COMMAND_CONTINUE_BAD;
	}

	item = NULL;
	if (opts & CMD_OPT_SEXPR) {
		if ( (item = read_sexpr (shul, scan)) == NULL) {
			printf ("Bad s-expression\n");
			return COMMAND_CONTINUE_BAD;
		}
	}

	cmdFunc (shul, item);
	if (item != NULL)
		sexpr_free (shul, item);

	return COMMAND_CONTINUE_GOOD;
}

static char *
stringScan (SCANNER * scan, void * ctx)
{
	char * line;

	scan->flags |= SF_WS;
	line = scan->ctx;
	scan->ctx = NULL; /* once only */
	return line;
}

static int
execCommand (SHULLIVAN * shul, char * cmd0)
{
	SCANNER scan;
	char * cmd = strdup (cmd0);
	int res;

	if (cmd == NULL)
		return -1;

	scannerInit (&scan, 
		     stringScan, cmd, 
		     freeLine,
		     scanToken, NULL, scanCleanup);

	res = command (shul, &scan);

	scan.cleanup (&scan);

	return res;
}

static void
shulSetPath (SHULLIVAN * shul, char * path)
{
	int delim;
	char * pch1;
	char * pch2;
	int len;

	delim = shul->delim;

	/* pass 1 - find out how many directories are in the path */
	pch1 = path;
	pch2 = path;
	len = 0;

	for (;;) {
		while (*pch2 != delim && *pch2 != '\0')
			++pch2;

		if (pch2 != pch1) {
			shul->ndirs++;
			len += (pch2 - pch1);
		}

		if (*pch2 == '\0')
			break;

		++pch2;
		pch1 = pch2;
	}

	if (shul->ndirs == 0)
		return;

	shul->path = malloc (shul->ndirs * (sizeof (char *) + 1) +  len);
	if (shul->path == NULL) {
		perror ("shulEnvRead:malloc");
		exit (1);
	}

	/* pass 2 - copy dir strings and store pointers */

	pch1 = path;
	pch2 = path;
	path = (char *)&shul->path[shul->ndirs];
	shul->ndirs = 0;

	for (;;) {
		while (*pch2 != delim && *pch2 != '\0')
			++pch2;

		if (pch2 != pch1) {
			shul->path[shul->ndirs++] = path;
			len = pch2 - pch1;
			memcpy (path, pch1, len);
			path[len] = '\0';
			path += len + 1;
		}

		if (*pch2 == '\0')
			break;

		++pch2; /* skip over delimiter */
		pch1 = pch2;
	}
}

static void
shulEnvRead (SHULLIVAN * shul)
{
	char * val;

	shul->path = NULL;
	shul->ndirs = 0;

	shul->delim = ':';

	val = getenv ("GHILBERT_PATH_DELIM");

	if (val != NULL)
		shul->delim = val[0];


	val = getenv ("GHILBERT_PATH");

	if (val != NULL)
		shulSetPath (shul, val);

	shul->flags = 0;

	val = getenv ("SHUL_FLAGS");
	if (val != NULL)
		shul->flags = strtoul (val, NULL, 0);
}

int
main (int argc, char * argv [])
{
	int interactive = 1;
	int result = 0;
	SCANNER scan;
	SHULLIVAN shul;
	int opt;

	memset (&shul, 0, sizeof (shul));

	shul.verbose = 1;

	shul.ndvvars = 16;
	shul.dvsize = BIT_MAP_SIZE (shul.ndvvars * (shul.ndvvars - 1) / 2);
	shul.histlen = 0;
	shul.histmax = HISTORY_TOP_LEVEL_SIZE;

	if (shulIdentInit() != 0 ||
	    growBufInit (&shul.vi, 16 * sizeof (EXPR_VARINFO)) != 0 ||
	    growBufInit (&shul.env, 32 * sizeof (EXPR *)) != 0 ||
	    growBufInit (&shul.dvw, 32 * sizeof (DVWORK)) != 0 ||
	    (shul.history = calloc (shul.histmax,
				    sizeof (*shul.history))) == NULL ||
	    (shul.dvbits = calloc (1, shul.dvsize)) == NULL ||
	    (shul.varIndex = mappingCreate (NULL)) == NULL ||
	    (shul.interfaces = mappingCreate (NULL)) == NULL ||
	    (shul.syms = mappingCreate(NULL)) == NULL ||
	    (shul.terms = mappingCreate(NULL)) == NULL ||
	    (shul.kinds = mappingCreate(NULL)) == NULL ||
	    (shul.fvi = mappingCreate (NULL)) == NULL ||
	    (shul.fvj = mappingCreate (NULL)) == NULL) {
		ALLOC_ERR ();
		/* for now, rely on unix to clean up after us */
		return 1;
	}

	shulEnvRead (&shul);

	while ((opt = getopt (argc, argv, "ze:v:V")) != -1) {
		switch (opt) {
		case 'z': /* command line only */
			interactive = 0;
			break;
		case 'e': /* execute interactive command */
			result = execCommand (&shul, optarg);
			if (result == COMMAND_ERR ||
			    result == COMMAND_CONTINUE_BAD) {
				fprintf (stderr, "Command Failed: %s\n",
					 optarg);
				return -1;
			}
			break;
		case 'v':
			shul.verbose = strtoul (optarg, NULL, 0);
			break;
		case 'V':
			printf ("Shullivan version %s\n", 
				SHULLIVAN_VERSION);
			break;
		case '?':
			exit (1);
			
		default:
			fprintf (stderr, "getopt returned 0x%x\n",
				 opt);
		}
	}

	if (interactive) {
		char * val;

		printf ("Shullivan version %s. "
			"Enter 'help' for help.\n", SHULLIVAN_VERSION);

		/* 
		 * realine doesn't work well in the emacs shell, which
		 * provides the desired functionality anyhow.
		 */
		if ((val = getenv ("EMACS")) &&
		    strcmp (val, "t") == 0 &&
		    (val = getenv ("TERM")) &&
		    strcmp (val, "dumb") == 0) {

			scannerInit (&scan, 
				     simpleScan, shulPrompt, 
				     freeLine,
				     scanToken, readlinePromptSet,
				     scanCleanup);

		} else {
			rl_bind_key ('\t', rl_insert);
			rl_bind_key ('\n', rl_insert);

			scannerInit (&scan, 
				     readlineScan, shulPrompt, 
				     freeLine,
				     scanToken, readlinePromptSet,
				     scanCleanup);
		}
		do {
			result = command (&shul, &scan);
		} while (result > COMMAND_EOF);

		scanCleanup (&scan);
	}

	return result;
}
