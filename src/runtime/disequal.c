#line 26 "disequal.nw"
#include "config.h"
#include "debug.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "eval.h"
#include "threads.h"
#include "spaces.h"
#include "unify.h"
#include "disequal.h"
#include "trail.h"
#include "cam.h"
#include "trace.h"

#define pair_cons_node_size constr_node_size(3)
static
NodeInfo pair_cons_info = {
    CONS_TAG, pair_cons_node_size, (const int *)0, (Label)eval_whnf, ",:", (FinalFun)0
};

DECLARE_LABEL(___61__47__61__1);
DECLARE_LABEL(___61__47__61__2);
DECLARE_LABEL(diseq_data);
DECLARE_LABEL(diseq_var);
DECLARE_LABEL(diseq_args);
#if YIELD_NONDET
DECLARE_LABEL(diseq_args_1);
#endif
DECLARE_LABEL(diseq_args_2);
DECLARE_LABEL(diseq_args_3);
DECLARE_LABEL(diseq_args_4);
DECLARE_LABEL(diseq_args_5);
DECLARE_LABEL(check_diseq);

#define diseq_constraint_size wordsof(Disequality)
NodeInfo diseq_constraint_info = {
    0, diseq_constraint_size, (const int *)0, (Label)check_diseq, (const char *)0,
    (FinalFun)0
};

FUNCTION(___61__47__61_)
{
    EXPORT_LABEL(___61__47__61_)
 ENTRY_LABEL(___61__47__61_)

    TRACE(("%I enter =/=%V\n", 2, sp));
    GOTO(___61__47__61__1);
}

static
FUNCTION(___61__47__61__1)
{
    Node *aux;

 ENTRY_LABEL(___61__47__61__1)
    EVAL_FLEX_POLY(___61__47__61__1);
    aux	  = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(___61__47__61__2);
}

static
FUNCTION(___61__47__61__2)
{
    unsigned int n;
    double	 d, e;
    Node	 *arg1, *arg2;

 ENTRY_LABEL(___61__47__61__2)
    EVAL_FLEX_POLY(___61__47__61__2);

    arg1 = sp[1];
    arg2 = sp[0];

    while ( is_boxed(arg1) && is_indir_node(arg1) )
	arg1 = arg1->n.node;
    if ( is_boxed(arg1) && is_variable_node(arg1) )
    {
	/* check for trivial disequality (x=/=x) */
	if ( arg1 == arg2 )
	    FAIL();
	sp[0] = arg1;
	sp[1] = arg2;
	GOTO(diseq_var);
    }
    else if ( is_boxed(arg2) && is_variable_node(arg2) )
    {
	sp[0] = arg2;
	sp[1] = arg1;
	GOTO(diseq_var);
    }
#if !ONLY_BOXED_OBJECTS
    else if ( is_unboxed(arg1) )
    {
	ASSERT(is_unboxed(arg2));
	if ( arg1 == arg2 )
	    FAIL();
    }
#endif
    else
    {
	ASSERT(is_boxed(arg2));
	if ( node_tag(arg1) == node_tag(arg2) )
	    switch ( node_tag(arg1) )
	    {
	    case CHAR_TAG:
		if ( arg1->ch.ch == arg2->ch.ch )
		    FAIL();
		break;
#if ONLY_BOXED_OBJECTS
	    case INT_TAG:
		if ( arg1->i.i == arg2->i.i )
		    FAIL();
		break;
#endif
	    case FLOAT_TAG:
		get_float_val(d, arg1->f);
		get_float_val(e, arg2->f);
		if ( d == e )
		    FAIL();
		break;

	    case PAPP_TAG:
		if ( arg1->info == arg2->info )
		{
		    if ( closure_argc(arg1) > 0 )
		    {
			sp[0] = arg1;
			sp[1] = arg2;
			GOTO(diseq_data);
		    }
		    FAIL();
		}
		break;

	    case SEARCH_CONT_TAG:
		if ( arg1 == arg2 )
		    FAIL();
		break;

	    default:
		ASSERT(is_constr_node(arg1) || is_abstract_node(arg1));
		if ( is_abstract_node(arg1) )
		{
		    if ( arg1 != arg2 )
			break;
		    n = 0;
		}
		else if ( is_vector(arg1) )
		{
		    if ( arg1->a.length != arg2->a.length )
			break;
		    n = vector_argc(arg1);
		}
		else
		    n = constr_argc(arg1);
		if ( n > 0 )
		{
		    sp[0] = arg1;
		    sp[1] = arg2;
		    GOTO(diseq_data);
		}
		FAIL();
        }
    }

    sp += 2;
    RETURN(Success);
}

#line 215 "disequal.nw"
static
FUNCTION(diseq_var)
{
    Node	*aux;
    Disequality *cstr;

 ENTRY_LABEL(diseq_var)
    if ( !is_local_space(sp[0]->v.spc) )
    {
	if ( is_boxed(sp[1]) && is_variable_node(sp[1])
	     && is_local_space(sp[1]->v.spc) )
	{
	    aux   = sp[0];
	    sp[0] = sp[1];
	    sp[1] = aux;
	}
	else
	    GOTO(delay_thread(___61__47__61__1, sp[0]));
    }

    if ( occurs(sp[0], sp[1]) )
    {
	sp += 2;
	RETURN(Success);
    }

    /* add the constraint to the variable */
    CHECK_HEAP(diseq_constraint_size);
    cstr	     = (Disequality *)hp;
    cstr->cstr.info  = &diseq_constraint_info;
    cstr->cstr.cstrs = sp[0]->v.cstrs;
    cstr->node	     = sp[1];
    hp		    += diseq_constraint_size;

    SAVE(sp[0], v.cstrs);
    sp[0]->v.cstrs = (Constraint *)cstr;

    /* evaluate the argument to normal form */
    sp[0] = sp[1];
    GOTO(___61__58__61_);
}

#line 297 "disequal.nw"
static
FUNCTION(diseq_data)
{
    boolean	 is_vect;
    unsigned int i, n;
    double	 d, e;
    Node	 *next, *arglist, *x, *y, **argp1, **argp2;
    word	 *oldHp;

 ENTRY_LABEL(diseq_data)

    is_vect = is_vector(sp[0]);
    n	    = is_vect ? vector_argc(sp[0]) : constr_argc(sp[0]);

    CHECK_HEAP(n * pair_cons_node_size);
    oldHp = hp;
    argp1 = is_vect ? sp[0]->a.args : sp[0]->c.args;
    argp2 = is_vect ? sp[1]->a.args : sp[1]->c.args;

    arglist = nil;
    argp1  += n;
    argp2  += n;
    for ( i = n; i-- > 0; )
    {
	x = *--argp1;
	y = *--argp2;
	while ( is_boxed(x) && is_indir_node(x) )
	    x = x->n.node;
	while ( is_boxed(y) && is_indir_node(y) )
	    y = y->n.node;

#if !ONLY_BOXED_OBJECTS
	if ( is_unboxed(x) )
	{
	    if ( is_unboxed(y) )
	    {
		if ( x != y )
		{
		    hp	= oldHp;
		    sp += 2;
		    RETURN(Success);
		}
		continue;
	    }
	}
	else
#endif /* !ONLY_BOXED_OBJECTS */
	    switch ( node_tag(x) )
	    {
	    case CHAR_TAG:
		if ( is_char_node(y) )
		{
		    if ( x->ch.ch != y->ch.ch )
		    {
			hp  = oldHp;
			sp += 2;
			RETURN(Success);
		    }
		    continue;
		}
		break;
#if ONLY_BOXED_OBJECTS
	    case INT_TAG:
		if ( is_int_node(y) )
		{
		    if ( int_val(x) != int_val(y) )
		    {
			hp  = oldHp;
			sp += 2;
			RETURN(Success);
		    }
		    continue;
		}
		break;
#endif /* ONLY_BOXED_OBJECTS */
	    case FLOAT_TAG:
		if ( is_float_node(y) )
		{
		    get_float_val(d, x->f);
		    get_float_val(e, y->f);
		    if ( d != e )
		    {
			hp  = oldHp;
			sp += 2;
			RETURN(Success);
		    }
		    continue;
		}
		break;
	    case VARIABLE_TAG:
		if ( x == y )
		    continue;
		break;
	    case PAPP_TAG:
		if ( is_papp_node(y) )
		{
		    if ( x->info != y->info )
		    {
			hp  = oldHp;
			sp += 2;
			RETURN(Success);
		    }
		    if ( closure_argc(x) == 0 )
			continue;
		}
		break;
	    case SEARCH_CONT_TAG:
		if ( is_search_cont_node(y) )
		{
		    if ( x != y )
		    {
			hp  = oldHp;
			sp += 2;
			RETURN(Success);
		    }
		    continue;
		}
	    case CLOSURE_TAG:
	    case SUSPEND_TAG:
	    case QUEUEME_TAG:
		break;
	    default:
		ASSERT(is_constr_node(x) || is_abstract_node(x));
		if ( is_constr_node(y) || is_abstract_node(y) )
		{
		    if ( node_tag(x) != node_tag(y) )
		    {
			hp  = oldHp;
			sp += 2;
			RETURN(Success);
		    }
		    if ( is_abstract_node(x) )
		    {
			if ( x != y )
			{
			    hp	= oldHp;
			    sp += 2;
			    RETURN(Success);
			}
			continue;
		    }
		    else if ( is_vector(x) )
		    {
			if ( x->a.length != y->a.length )
			{
			    hp	= oldHp;
			    sp += 2;
			    RETURN(Success);
			}
			if ( vector_argc(x) == 0 )
			    continue;
		    }
		    else if ( constr_argc(x) == 0 )
			continue;
		    break;
		}
		break;
	    }

	next		= (Node *)hp;
	next->c.info	= &pair_cons_info;
	next->c.args[0] = x;
	next->c.args[1] = y;
	next->c.args[2] = arglist;
	arglist		= next;
	hp	       += pair_cons_node_size;
    }

    if ( arglist == nil )
	FAIL();

    *++sp = arglist;
    GOTO(diseq_args);
}

#line 482 "disequal.nw"
static Label diseq_args_choices[] = { diseq_args_2, diseq_args_3, (Label)0 };

static
FUNCTION(diseq_args)
{
 ENTRY_LABEL(diseq_args)
    ASSERT(sp[0]->info == &pair_cons_info);

    if ( sp[0]->c.args[2] == nil )
	GOTO(diseq_args_2);

#if YIELD_NONDET
    if ( rq != (ThreadQueue)0 )
        GOTO(yield_thread(diseq_args_1));
#endif
    choice_conts = diseq_args_choices;
    GOTO(nondet_handlers.choices);
}

#if YIELD_NONDET
static
FUNCTION(diseq_args_1)
{
 ENTRY_LABEL(diseq_args_1)
    choice_conts = diseq_args_choices;
    GOTO(nondet_handlers.choices);
}
#endif

static
FUNCTION(diseq_args_2)
{
    Node *arglist;

 ENTRY_LABEL(diseq_args_2)
    CHECK_STACK1();
    arglist = sp[0];
    sp	   -= 1;
    sp[0]   = arglist->c.args[0];
    sp[1]   = arglist->c.args[1];
    GOTO(___61__47__61_);
}

static
FUNCTION(diseq_args_3)
{
    Node *susp, *arglist;

 ENTRY_LABEL(diseq_args_3)
    CHECK_STACK(6);
    CHECK_HEAP(queueMe_node_size);

    arglist = sp[0];

    susp	= (Node *)hp;
    susp->info	= &queueMe_info;
    susp->q.wq	= (ThreadQueue)0;
    susp->q.spc	= ss;
    hp	       += queueMe_node_size;

    sp	 -= 6;
    sp[0] = arglist->c.args[0];
    sp[1] = arglist->c.args[1];
    sp[2] = (Node *)update;
    sp[3] = susp;
    sp[4] = (Node *)diseq_args_4;
    sp[5] = susp;
    sp[6] = arglist->c.args[2];
    start_thread(5);
    GOTO(___61__58__61_);
}

static
FUNCTION(diseq_args_4)
{
    Node *r;

 ENTRY_LABEL(diseq_args_4)
    for ( r = sp[0]; node_tag(r) == INDIR_TAG; r = r->n.node )
	;

    if ( node_tag(r) == SUCCESS_TAG )
	sp++;
    else
    {
	ASSERT(node_tag(r) == QUEUEME_TAG);
	CHECK_STACK1();
	sp   -= 1;
	sp[0] = sp[2];
	sp[1] = (Node *)diseq_args_5;
	sp[2] = r;
    }
    GOTO(diseq_args);
}

static
FUNCTION(diseq_args_5)
{
    Node *r;

 ENTRY_LABEL(diseq_args_5)
    ASSERT(node_tag(sp[0]) == SUCCESS_TAG);

    for ( r = sp[1]; node_tag(r) == INDIR_TAG; r = r->n.node )
	;
    if ( node_tag(r) == QUEUEME_TAG )
    {
	*++sp = r;
	GOTO(r->info->eval);
    }
    ASSERT(node_tag(r) == SUCCESS_TAG);

    sp += 2;
    RETURN(r);
}

#line 603 "disequal.nw"
static
FUNCTION(check_diseq)
{
 ENTRY_LABEL(check_diseq)
    sp[1] = ((Disequality *)sp[1])->node;
    GOTO(___61__47__61_);
}
