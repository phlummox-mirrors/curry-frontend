#line 13 "random.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <sys/time.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "eval.h"
#include "io_monad.h"
#include "cam.h"
#include "trace.h"

#define pair_node_size	 constr_node_size(2)
#define pair_info	 ___40__44__41__info

static DEFINE_DATA(___40__44__41_, "(,)", 0, 2);

#line 39 "random.nw"
#define STATESIZE 128

#line 50 "random.nw"
#define STDGEN_TAG	 ABSTRACT_TAG
#define stdgen_node_size wordsof(StdGen)

static void finalize_stdgen(Node *);

typedef struct stdgen_node {
    NodeInfo *info;
    int	     random;		/* buffer for random bits */
    int      valid;		/* number of valid bits in the buffer */
    char     *state;
} StdGen;

static NodeInfo stdgen_info = {
    STDGEN_TAG, stdgen_node_size, ot_binary, (Label)eval_whnf,
    "<<Random.StdGen>>", finalize_stdgen
};

static void
finalize_stdgen(Node *node)
{
    StdGen *rng = (StdGen *)node;

    free(rng->state);
}

#line 82 "random.nw"
DECLARE_ENTRYPOINT(__mkStdGen);

FUNCTION(__mkStdGen)
{
    unsigned long seed;
    StdGen	  *rng;

    EXPORT_LABEL(__mkStdGen)
 ENTRY_LABEL(__mkStdGen)
    EVAL_RIGID_INT(__mkStdGen);

    seed = int_val(sp[0]);
    sp	+= 1;

    CHECK_HEAP(stdgen_node_size);
    rng		= (StdGen *)hp;
    rng->info   = &stdgen_info;
    rng->state  = (char *)malloc(STATESIZE);
    rng->valid  = 0;
    rng->random = 0;
    hp	       += stdgen_node_size;

    if ( rng->state == (char *)0 )
    {
	fprintf(stderr, "mkStdGen: memory exhausted\n");
	exit(1);
    }
    setstate(initstate(seed, rng->state, STATESIZE));
    RETURN((Node *)rng);
}

#line 137 "random.nw"
DECLARE_ENTRYPOINT(__nextStdGen);
DECLARE_ENTRYPOINT(__nextRStdGen);

DECLARE_LABEL(__nextRStdGen_1);
DECLARE_LABEL(__nextRStdGen_2);

#if ONLY_BOXED_OBJECTS
static struct int_node minInt_node = { &int_info, LONG_MIN };
static struct int_node maxInt_node = { &int_info, LONG_MAX };

# define minInt (Node *)&minInt_node
# define maxInt (Node *)&maxInt_node
#else
# define minInt mk_int(LONG_MIN/2)
# define maxInt mk_int(LONG_MAX/2)
#endif

FUNCTION(__nextStdGen)
{
    EXPORT_LABEL(__nextStdGen)
 ENTRY_LABEL(__nextStdGen)
    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = sp[2];
    sp[1] = minInt;
    sp[2] = maxInt;
    GOTO(__nextRStdGen_2);
}

FUNCTION(__nextRStdGen)
{
    Node *lo, *hi;
    EXPORT_LABEL(__nextRStdGen)
 ENTRY_LABEL(__nextRStdGen)
    EVAL_RIGID_INT(__nextRStdGen);
    lo	  = sp[0];
    hi	  = sp[1];
    sp[0] = hi;
    sp[1] = lo;
    GOTO(__nextRStdGen_1);
}

static
FUNCTION(__nextRStdGen_1)
{
    Node *rng, *hi;
 ENTRY_LABEL(__nextRStdGen_1)
    EVAL_RIGID_INT(__nextRStdGen_1);
    hi	  = sp[0];
    rng	  = sp[2];
    sp[0] = rng;
    sp[2] = hi;
    GOTO(__nextRStdGen_2);
}

static
FUNCTION(__nextRStdGen_2)
{
    char   *o;
    int    bits;
    long   lo, hi, r;
    unsigned long diff, mask;
    StdGen *rng;
    Node   *p, *i;

 ENTRY_LABEL(__nextRStdGen_2)
    EVAL_RIGID(__nextRStdGen_2);

    CHECK_HEAP(pair_node_size + int_node_size);

    rng	= (StdGen *)sp[0];
    lo	= int_val(sp[1]);
    hi	= int_val(sp[2]);
    sp += 3;

    /* determine the number of bits required */
    if ( hi >= lo )
    {
	diff = hi - lo;
	mask = 1;
	for (bits = 1; diff & ~mask; bits++)
	    mask = (mask << 1) + 1;
    }
    else
	FAIL();

    o = setstate(rng->state);
repeat:
    r = 0;
    while ( rng->valid < bits )
    {
    	bits	   -= rng->valid;
     	mask	  >>= rng->valid;
   	r	   |= rng->random << bits;
    	rng->random = random();
	rng->valid  = 31;
    }
    r		 |= rng->random & mask;
    rng->valid   -= bits;
    rng->random >>= bits;
    r		 += lo;
    if ( r > hi )
	goto repeat;
    setstate(o);

#if ONLY_BOXED_OBJECTS
    i	    = (Node *)hp;
    i->info = &int_info;
    i->i.i  = r;
    hp	   += int_node_size;
#else
    i = mk_int(r);
#endif

    p		 = (Node *)hp;
    p->info	 = &pair_info;
    p->c.args[0] = i;
    p->c.args[1] = (Node *)rng;
    hp		+= pair_node_size;

    RETURN(p);
}

#line 265 "random.nw"
FUNCTION(__genRange)
{
    Node *r;
    EXPORT_LABEL(__genRange)
 ENTRY_LABEL(__genRange)
    sp		+= 1;

    CHECK_HEAP(pair_node_size);
    r		 = (Node *)hp;
    r->info	 = &pair_info;
    r->c.args[0] = minInt;
    r->c.args[1] = maxInt;
    hp		+= pair_node_size;

    RETURN(r);
}

#line 303 "random.nw"
static StdGen *stdGen;

#define DET_CHECK(what) do { \
    if ( bp != (Choicepoint *)0 ) { \
	fprintf(stderr, "Cannot duplicate " what "\n"); \
	curry_exit(1); \
    } \
} while (0)

DECLARE_ENTRYPOINT(__setStdGen);

FUNCTION(__setStdGen)
{
    EXPORT_LABEL(__setStdGen)
 ENTRY_LABEL(__setStdGen)
    EVAL_RIGID(__setStdGen);
    if ( stdGen == (StdGen *)0 )
	add_global_root((Node **)&stdGen);
    DET_CHECK("Random.stdGen");
    stdGen = (StdGen *)sp[0];
    sp	  += 2;
    RETURN(unit);
}

DECLARE_ENTRYPOINT(__getStdGen);
DECLARE_LABEL(__getStdGen_1);

FUNCTION(__getStdGen)
{
    long	   seed;
    struct timeval tv;
#if ONLY_BOXED_OBJECTS
    static struct int_node seed_node = { &int_info, 0 };
#endif
    EXPORT_LABEL(__getStdGen)
 ENTRY_LABEL(__getStdGen)
    if ( stdGen != (StdGen *)0 )
    {
	sp += 1;
	RETURN((Node *)stdGen);
    }

    gettimeofday(&tv, (struct timezone *)0);
    srandom(tv.tv_sec ^ tv.tv_usec);
    seed = random();

    CHECK_STACK1();
    sp -= 1;
#if ONLY_BOXED_OBJECTS
    seed_node.i = seed;
    sp[0]	= (Node *)&seed_node;
#else
    sp[0] = mk_int(seed);
#endif
    sp[1] = (Node *)__getStdGen_1;
    GOTO(__mkStdGen);
}

static
FUNCTION(__getStdGen_1)
{
    Node *rng;
 ENTRY_LABEL(__getStdGen_1)
    rng = *sp++;
    add_global_root((Node **)&stdGen);
    DET_CHECK("Random.stdGen");
    stdGen = (StdGen *)rng;
    RETURN(rng);
}
