#line 14 "compare.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "eval.h"
#include "threads.h"
#include "cam.h"
#include "trace.h"

DECLARE_CONST(__prelude__LT);
DECLARE_CONST(__prelude__EQ);
DECLARE_CONST(__prelude__GT);

#define prelude_LT (Node *)&__prelude__LT_node
#define prelude_EQ (Node *)&__prelude__EQ_node
#define prelude_GT (Node *)&__prelude__GT_node

#define pair_cons_node_size constr_node_size(3)
static
NodeInfo pair_cons_info = {
    CONS_TAG, pair_cons_node_size, (const int *)0, (Label)eval_whnf, ",:", (FinalFun)0
};

DECLARE_ENTRYPOINT(__compare);

DECLARE_LABEL(__compare_1);
DECLARE_LABEL(__compare_2);
DECLARE_LABEL(__compare_3);

FUNCTION(__compare)
{
    EXPORT_LABEL(__compare)
 ENTRY_LABEL(__compare)

    TRACE(("%I enter compare%V\n", 2, sp));
    GOTO(__compare_1);
}

static
FUNCTION(__compare_1)
{
    Node *aux;

 ENTRY_LABEL(__compare_1)
    EVAL_RIGID_POLY(__compare_1);
    aux	  = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(__compare_2);
}

static
FUNCTION(__compare_2)
{
    boolean	 is_vect;
    long         x, y;
    unsigned int i, n;
    double	 d, e;
    Node	 *cmp;
    Node	 *arg1, *arg2;
    Node	 *next, *arglist;
    Node	 **argp1, **argp2;

 ENTRY_LABEL(__compare_2)
    EVAL_RIGID_POLY(__compare_2);

    n	    = 0;
    arg1    = sp[1];
    arg2    = sp[0];
    is_vect = false;

#if !ONLY_BOXED_OBJECTS
    if ( is_unboxed(arg1) )
    {
	ASSERT(is_unboxed(arg2));
	x = (long)arg1;
	y = (long)arg2;
	cmp = x == y ? prelude_EQ : x < y ? prelude_LT : prelude_GT;
    }
    else
#endif
    {
	ASSERT(is_boxed(arg2));
	switch ( node_tag(arg1) )
	{
	case CHAR_TAG:
	    ASSERT(is_char_node(arg2));
	    x = arg1->ch.ch;
	    y = arg2->ch.ch;
	    cmp = x == y ? prelude_EQ : x < y ? prelude_LT : prelude_GT;
	    break;
#if ONLY_BOXED_OBJECTS
        case INT_TAG:
	    ASSERT(is_int_node(arg2));
	    x = int_val(arg1);
	    y = int_val(arg2);
	    cmp = x == y ? prelude_EQ : x < y ? prelude_LT : prelude_GT;
	    break;
#endif
        case FLOAT_TAG:
	    ASSERT(is_float_node(arg2));
	    get_float_val(d, arg1->f);
	    get_float_val(e, arg2->f);
	    cmp = d == e ? prelude_EQ : d < e ? prelude_LT : prelude_GT;
            break;

        default:
	    if ( !is_constr_node(arg1) || !is_constr_node(arg2) )
	    	FAIL();
	    x = (long)node_tag(arg1);
	    y = (long)node_tag(arg2);
	    if ( x == y )
	    {
		cmp = prelude_EQ;
		if ( is_vector(arg1) )
		{
		    is_vect = true;
		    x = arg1->a.length;
		    y = arg2->a.length;
		    if ( x == y )
			n = vector_argc(arg1);
		    else
			cmp = x < y ? prelude_LT : prelude_GT;
		}
		else
		    n = constr_argc(arg1);
	    }
	    else
		cmp = x < y ? prelude_LT : prelude_GT;
            break;
        }
    }

    if ( cmp != prelude_EQ || n == 0 )
    {
	sp += 2;
	RETURN(cmp);
    }
    else if ( n == 1 )
    {
	sp[0] = is_vect? arg1->a.args[0] : arg1->c.args[0];
	sp[1] = is_vect? arg2->a.args[0] : arg2->c.args[0];
	GOTO(__compare);
    }

    arglist = nil;
    CHECK_HEAP(n * pair_cons_node_size);
    argp1 = is_vect ? sp[1]->a.args : sp[1]->c.args;
    argp2 = is_vect ? sp[0]->a.args : sp[0]->c.args;

    for ( i = n, argp1 += n, argp2 += n; i-- > 1; )
    {
	next		= (Node *)hp;
	next->c.info	= &pair_cons_info;
	next->c.args[0] = *--argp1;
	next->c.args[1] = *--argp2;
	next->c.args[2] = arglist;
	arglist		= next;
	hp	       += pair_cons_node_size;
    }

    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = *--argp1;
    sp[1] = *--argp2;
    sp[2] = (Node *)__compare_3;
    sp[3] = arglist;
    GOTO(__compare);
}

static
FUNCTION(__compare_3)
{
    Node *cmp, *arg1, *arg2, *arglist;

 ENTRY_LABEL(__compare_3)

    cmp = sp[0];
    if ( cmp != prelude_EQ )
    {
	sp += 2;
	RETURN(cmp);
    }

    ASSERT(sp[1]->info == &pair_cons_info);
    arglist = sp[1];
    arg1    = arglist->c.args[0];
    arg2    = arglist->c.args[1];
    arglist = arglist->c.args[2];

    if ( arglist == nil )
    {
	sp[0] = arg1;
	sp[1] = arg2;
	GOTO(__compare);
    }

    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = arg1;
    sp[1] = arg2;
    sp[2] = (Node *)__compare_3;
    sp[3] = arglist;
    GOTO(__compare);
}
