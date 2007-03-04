/* shullivan.h - C implementation header for Ghilbert proof checker */

#ifndef __INCshullivanh
#define __INCshullivanh

#define SHULLIVAN_VERSION "0.05"

/*
 * Lexical items - identifiers and s-lists
 * An identifier is a sequence of non-white-space characters other
 * than '(' and ')' and '#', without any interpretation of its use as a
 * kind, variable, term name, theorem or axiom name, or hypothesis
 * name.
 * 
 * (Ugh: identifiers are currently also used as file names, and there's
 * no way to escape a space character or other special character in
 * a file name.)
 * 
 * IDENT := id-char | id-char IDENT
 *
 * An s-list is the lexical format of an s-expression, without the type
 * information and term checking. Note, however, that at this level we
 * allow "()", "((whee) 7)", and other expressions which couldn't be
 * valid ghilbert terms, because the first member of the list isn't an
 * ident/term symbol.
 * 
 * COMMENT_WS := '#' NON_NEWLINES '\n'
 * NON_NEWLINES := empty | non-'\n'-character NON_NEWLINES
 * WS_CHAR := whitespace-character | COMMENT_WS
 * WS := WS_CHAR | WS_CHAR WS
 * OWS := empty | WS
 * 
 * A comment is also allowed to terminate at EOF without the trailing
 * '\n'.
 *
 * SLIST := IDENT | '(' OWS SLIST_OSEQ OWS ')'
 * SLIST_SEQ := SLIST | SLIST WS SLIST_SEQ
 * SLIST_OSEQ := empty | SLIST_SEQ
 */

#include <limits.h>
#include <stdint.h>

#include "arena.h"
#include "shul_ident.h"


typedef struct _SYMBOL SYMBOL;

typedef enum _ITEM_TYPE {
	IT_IDENT,
	IT_SLIST
} ITEM_TYPE;

typedef union _ITEM ITEM;

typedef struct _GENERIC_ITEM {
	ITEM_TYPE itype;
	ITEM * next;	/* Items may be in one intrinsic list */
} GENERIC_ITEM;

typedef struct _SLIST_ITEM {
	GENERIC_ITEM it;
	ITEM * first;  /* NULL for an empty SLIST */
} SLIST_ITEM;

typedef struct _IDENT_ITEM {
	GENERIC_ITEM it;
	IDENT * id;
} IDENT_ITEM;

union _ITEM {
	GENERIC_ITEM it;
	SLIST_ITEM sl;
	IDENT_ITEM id;
};

/*
 * Identifier scopes:
 *
 * Kind names are in their own scope.
 *
 * Terms and definition names are in a scope together. These
 * names occur only as the first item of an S-EXPR list, and
 * as such are not confoundable with other types of identifiers.
 *
 * Proof steps may be:
 *  - names of theorems (or other proven/assumed statements)
 *  - variables (these go on the wild variable stack for a
 *    statement to be applied in a subsequent proof step)
 *  - names of hypotheses of the theorem being proved
 * and
 *  - non-identifier S-expressions.
 *
 * The non-identifier S-expressions are distinguishable from the others,
 * and like variable names, go onto the wild variable stack for
 * use by subsequent theorem references.
 *
 * The scope of a hypothesis name is just the theorem itself.
 * A proof step which matches a hyothesis name is taken to be the
 * hypothesis name in preference to a theorem name or variable
 * name, if it matches either of those as well as the hypothesis name.
 * It is an error if an identifier which is a hypothesis name for a
 * theorem appears also as a variable in the hypotheses or conclusions
 * of a theorem. (It is also an error if the same identifier is used
 * as the name for more than one hypothesis of the same theorem.)
 *
 * If an identifier appears as a variable in either the hypotheses
 * or the conclusions of a theorem, it will be treated as a variable
 * if it occurs as a proof step of that theorem, even if there is
 * also an accepted statement of the same name. If an identifier
 * appears in a proof step which is not a hypothesis name and also
 * does not occur as a variable in the hypotheses or conclusions of
 * the theorem, then if there is an accepted statement of that name,
 * the identifier is taken as a statement reference; otherwise, if
 * there is a global variable declaration of that name, the identifier
 * is taken as the variable; otherwise, it is an error.
 */

typedef struct _INTERFACE INTERFACE;

/*
 * Each kind equivalence class has a representative which is the
 * earliest* kind in the equivalence class. Each member of
 * an equivalence class has a pointer to the representative of that
 * class.  When a .ghi kindbind is done, this links two equivalence
 * classes (if not already linked). The new representative will
 * be the earlier* of the current representatives of the two classes;
 * all the kinds in the old class not containing that representative
 * will be updated to point to the new representative.
 *
 * *'earliest' in some convenient ordering (which is not critical)
 * We use the address of the kind data structure, choosing as the
 * representative of a class that kind in the class with the
 * numerically lowest address.  Since each kind starts out in a class
 * by itself, we only need to adjust the representatives when doing
 * (or backing out) a kindbind, or removing a kind added earlier (if
 * we were to allow that).
 */

typedef struct _KIND KIND;

struct _KIND {
	IDENT * id;		/* initial identifier for this kind */
	INTERFACE * iface;	/* interface which added this kind */
	KIND * rep;		/* kind equiv. class representative */
};

typedef enum _SYMBOL_TYPE {
	ST_UNK,		/* Unknown or as yet undetermined symbol type */
	ST_INTERFACE,	/* an interface */

	ST_TERM,	/* Term symbol name: constant/function/relation/
			   logical connective */
	ST_DEF,		/* defined term */

	ST_STMT,	/* Statement name */
	ST_VAR,		/* Variable name */
} SYMBOL_TYPE;

struct _SYMBOL {
	SYMBOL_TYPE stype;
	IDENT * ident;		/* back pointer to identifier */
};

typedef union _EXPR EXPR;

/*
 * Generic expression type. Variables and S-Expressions are the two
 * classes of expressions. Every expression has a unique kind.
 */

typedef enum _EXPR_TYPE {
	ET_VAR,
	ET_IVAR,	/* variable specified by index, implicitly
			   within the context of a statement or
			   a definition */
	ET_SEXPR
} EXPR_TYPE;

typedef struct _EXPR_CORE {
	EXPR_TYPE etype;
	KIND * kind;
} EXPR_CORE;

typedef struct _EXPR_VARINFO {
	EXPR_CORE ex;	/* ex.type = ET_IVAR */
	int index;
	IDENT * id;
} EXPR_VARINFO;

typedef struct _VAR {
	EXPR_CORE ex;	/* ex.type = ET_VAR */
	SYMBOL sym;	/* variable name */
} VAR;

#define SYM2VAR(x) ((VAR *)((char *)(x) - offsetof (VAR, sym)))

typedef struct _TERM {
	SYMBOL sym;
	INTERFACE * iface;	/* interface which added this term */
	KIND * kind;		/* term value kind */
	int arity;		/* number of term parameters */
	KIND ** kinds;		/* term parameter kinds */
} TERM;

/* Note, def's are not allowed in .ghi files */
typedef struct _DEF {
	TERM t;		/* Some duplication ... */
	int ndummies;	/* Number of dummy variables of the definition.
			   This is the number of different variables
			   appearing in the definiens, which do not
			   appear in the formal parameter list */
	EXPR * expr;	/* expression of definiens */
	EXPR_VARINFO vi[1];	/* Variable length, t->arity + ndummies
				   entries. */
} DEF;

typedef struct _S_EXPR {
	EXPR_CORE ex;	/* ex.type = ET_SEXPR */
	TERM * t;
	EXPR * args[1];	/* Variable length. Array of t->arity 
			   EXPR *'s */
} S_EXPR;


/* A Ghilbert proof interface (represents a .ghi file import) */

struct _INTERFACE {
	SYMBOL sym;

	int nparams;
	INTERFACE ** params;	/* table of all parameter interfaces */

	IDENT_TABLE * kinds;	/* kinds added by this interface. */
	IDENT_TABLE * terms;	/* terms added by this interface. */
	MAPPING * origKinds;	/* for undoing kindbinds by the interface */

	char * prefix;		/* prefix */
	int pfxlen;		/* prefix length, not counting NUL */
	IDENT * fileId;		/* identifier with filename/URL */
	int import;		/* 1 --> import; 0 --> export */
};

union _EXPR {
	EXPR_CORE ex;
	EXPR_VARINFO vi;
	VAR var;
	S_EXPR sx;
};

#define BITMAP_WORDBYTES (sizeof (uint32_t))
#define BITMAP_WORDBITS  (sizeof (uint32_t) * CHAR_BIT)

#define BIT_MAP_SIZE(x) \
  ((((x) + BITMAP_WORDBITS - 1) / BITMAP_WORDBITS) * BITMAP_WORDBYTES)

/*
 * Distinct variables bitmaps.  When there are n free variables in
 * the hypotheses and conclusions, there are n * (n-1) / 2 possible
 * pairs of variables (i,j), considered as indices 0 <= i < j < n.
 * Note that the map (i,j) -> p(i,j) = j * (j-1)/2 + i is a bijection
 * from this set of pairs to {0, ..., n*(n-1)/2 - 1}, and we use
 * this map to select a bit in the bitmap.
 */
#define PAIRNUM(i, j) (((j) * ((j) - 1) / 2) + (i))

#define BIT(m, x) \
  ((m)[(x)/BITMAP_WORDBITS] & (1 << ((x) & (BITMAP_WORDBITS - 1)))) 
#define BIT_SET(m, x) \
  ((m)[(x)/BITMAP_WORDBITS] |= (1 << ((x) & (BITMAP_WORDBITS - 1)))) 
#define BIT_CLR(m, x) \
  ((m)[(x)/BITMAP_WORDBITS] &= ~(1 << ((x) & (BITMAP_WORDBITS - 1)))) 

typedef struct _THEOREM THEOREM;

typedef struct _STATEMENT {
	SYMBOL		sym;	/* ident, stype */
	INTERFACE *	iface;	/* interface which added statement;
				   NULL if added in .gh file */
	int		nHyps;	/* number of hypotheses */
	EXPR **		hyps;	/* array of hypotheses */
	int		nCons;	/* number of conclusions */
	EXPR **		cons;	/* array of conclusions */
	int		nhvars;	/* number of different variables
				   occurring in the hypotheses. */
	int		nWild;	/* Number of 'wild' variables. */
	uint32_t *	dvbits; /* pointer to distinct var bitmap */
	THEOREM *	thm;	/* NULL unless this is a theorem */

	EXPR_VARINFO vi [1];	/* 
				   Variable length array. Must be last.
				   Information for the nhvars +
				   nWild variables (in order with
				   wild variables last). The kinds
				   are critical, particularly for
				   the wild variables, but the
				   identifiers are needed only for
				   show routines or error messages to
				   the user. They will not be in the
				   global symbol table if the statement
				   came from an import. */
} STATEMENT;

typedef enum _STEP_TYPE {
	STEPT_REF,	/* Reference to proved theorem or axiom */
	STEPT_EXPR,	/* Expression for wild hyp/variable */
	STEPT_HYP	/* Reference to theorem hypothesis */
} STEP_TYPE;

typedef struct _STEP {
	STEP_TYPE type;
} STEP;

typedef struct _STEP_EXPR {
	STEP	s;
	EXPR *	x;
} STEP_EXPR;

typedef struct _STEP_REF {
	STEP		s;
	STATEMENT *	stat;
} STEP_REF;

typedef struct _STEP_HYP {
	STEP	s;
	int	index;	/* index into theorem's hypothesis array */
} STEP_HYP;

typedef union _PROOF_STEP {
	STEP		s;
	STEP_EXPR	expr;
	STEP_HYP	hyp;
	STEP_REF	ref;
} PROOF_STEP;

/*
 * A proven theorem in the database, for which we want to remember
 * the proof.
 */

struct _THEOREM {
	STATEMENT *	stmt;
	int		nSteps;	/* number of steps in the proof */
	PROOF_STEP *	steps;	/* Array of proof steps */
	IDENT *	hypnam[1];	/* variable length array of hypothesis
				   names. stmt->nHyps entries. */
};

typedef struct _EXPR_STACK {
	int count;	/* number of items currently on the stack */
	int maxsize;	/* maximum number of items allowed */
	EXPR ** exprs;	/* Array of expressions */
	ARENA * arena;
} EXPR_STACK;

/*
 * Mapping from the variables occurring in a statement's formal
 * hypotheses and its wild hypothesis variables, to expressions.
 */
typedef struct _ENVIRONMENT {
	void * TBD;
} ENVIRONMENT;

/* A theorem in progress */

typedef struct _TIP {
	THEOREM *	t;
	STATEMENT *	s;	/* shortcut to t->stmt */
	EXPR_STACK	ps;	/* the proof stack (list?) */
	EXPR_STACK	wvs;	/* stack for wild variable substitutions */
	IDENT_TABLE *   hypnams;	/* hypothesis name lookup table */
	IDENT_TABLE *	varIndex;	/* variable lookup */
	int		step;   /* current proof step number */
	ARENA arena;		/* expression memory storage in proof */
} TIP;

#endif /* __INCshullivanh */
