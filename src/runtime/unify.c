#line 23 "unify.nw"
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
#include "trail.h"
#include "unify.h"
#include "cam.h"
#include "trace.h"

#define pair_cons_node_size constr_node_size(3)
static
NodeInfo pair_cons_info = {
    CONS_TAG, pair_cons_node_size, (const int *)0, (Label)eval_whnf,
    ",:", (FinalFun)0
};

DECLARE_LABEL(___61__58__61__1);
DECLARE_LABEL(___61__58__61__2);
DECLARE_LABEL(unify_data);
DECLARE_LABEL(unify_var);
DECLARE_LABEL(unify_args);
DECLARE_LABEL(unify_args_1);
DECLARE_LABEL(unify_args_2);


FUNCTION(___61__58__61_)
{
    EXPORT_LABEL(___61__58__61_)
 ENTRY_LABEL(___61__58__61_)

    TRACE(("%I enter =:=%V\n", 2, sp));
    GOTO(___61__58__61__1);
}

static
FUNCTION(___61__58__61__1)
{
    Node *aux;

 ENTRY_LABEL(___61__58__61__1)
    EVAL_FLEX_POLY(___61__58__61__1);
    aux	  = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(___61__58__61__2);
}

static
FUNCTION(___61__58__61__2)
{
    unsigned int n;
    double	 d, e;
    Node	 *arg1, *arg2;

 ENTRY_LABEL(___61__58__61__2)
    EVAL_FLEX_POLY(___61__58__61__2);

    arg1 = sp[1];
    arg2 = sp[0];

    while ( is_boxed(arg1) && is_indir_node(arg1) )
	arg1 = arg1->n.node;
    if ( is_boxed(arg1) && is_variable_node(arg1) )
    {
	/* check for trivial unification */
	if ( arg1 != arg2 )
	{
	    sp[0] = arg1;
	    sp[1] = arg2;
	    GOTO(unify_var);
	}
    }
    else if ( is_boxed(arg2) && is_variable_node(arg2) )
    {
	sp[0] = arg2;
	sp[1] = arg1;
	GOTO(unify_var);
    }
#if !ONLY_BOXED_OBJECTS
    else if ( is_unboxed(arg1) )
    {
	ASSERT(is_unboxed(arg2));
	if ( arg1 != arg2 )
	    FAIL();
    }
#endif
    else
    {
	ASSERT(is_boxed(arg2));
	if ( node_tag(arg1) != node_tag(arg2) )
	    FAIL();
	switch ( node_tag(arg1) )
	{
	case CHAR_TAG:
	    if ( arg1->ch.ch != arg2->ch.ch )
		FAIL();
	    break;
#if ONLY_BOXED_OBJECTS
	case INT_TAG:
	    if ( arg1->i.i != arg2->i.i )
		FAIL();
	    break;
#endif
        case FLOAT_TAG:
	    get_float_val(d, arg1->f);
	    get_float_val(e, arg2->f);
	    if ( d != e )
		FAIL();
	    break;

        case PAPP_TAG:
	    if ( arg1->info != arg2->info )
		FAIL();
	    if ( closure_argc(arg1) > 0 )
	    {
		sp[0] = arg1;
		sp[1] = arg2;
		GOTO(unify_data);
	    }
	    break;

        case SEARCH_CONT_TAG:
	    if ( arg1 != arg2 )
		FAIL();
	    break;

        default:
	    ASSERT(is_constr_node(arg1) || is_abstract_node(arg1));
	    if ( is_abstract_node(arg1) )
	    {
		if ( arg1 != arg2 )
		    FAIL();
		n = 0;
	    }
	    else if ( is_vector(arg1) )
	    {
		if ( arg1->a.length != arg2->a.length )
		    FAIL();
		n = vector_argc(arg1);
	    }
	    else
		n = constr_argc(arg1);
	    if ( n > 0 )
	    {
		sp[0] = arg1;
		sp[1] = arg2;
		GOTO(unify_data);
	    }
        }
    }

    sp += 2;
    RETURN(Success);
}

#line 200 "unify.nw"
static
FUNCTION(unify_data)
{
    boolean	 is_vect;
    unsigned int i, n;
    double	 d, e;
    Node	 *next, *arglist, *x, *y, **argp1, **argp2;

 ENTRY_LABEL(unify_data)

    is_vect = is_vector(sp[0]);
    n	    = is_vect ? vector_argc(sp[0]) : constr_argc(sp[0]);

    CHECK_HEAP(n * pair_cons_node_size);
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
		    FAIL();
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
			FAIL();
		    continue;
		}
		break;
#if ONLY_BOXED_OBJECTS
	    case INT_TAG:
		if ( is_int_node(y) )
		{
		    if ( int_val(x) != int_val(y) )
			FAIL();
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
			FAIL();
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
			FAIL();
		    if ( closure_argc(x) == 0 )
			continue;
		}
		break;
	    case SEARCH_CONT_TAG:
		if ( is_search_cont_node(y) )
		{
		    if ( x != y )
			FAIL();
		    continue;
		}
		break;
	    case CLOSURE_TAG:
	    case SUSPEND_TAG:
	    case QUEUEME_TAG:
		break;
	    default:
		ASSERT(is_constr_node(x) || is_abstract_node(x));
		if ( is_constr_node(y) || is_abstract_node(y) )
		{
		    if ( node_tag(x) != node_tag(y) )
			FAIL();
		    if ( is_abstract_node(x) )
		    {
			if ( x != y )
			    FAIL();
			continue;
		    }
		    else if ( is_vector(x) )
		    {
			if ( x->a.length != y->a.length )
			    FAIL();
			if ( vector_argc(x) == 0 )
			    continue;
		    }
		    else if ( constr_argc(x) == 0 )
			continue;
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

    if ( arglist != nil )
    {
	*++sp = arglist;
	GOTO(unify_args);
    }
    sp += 2;
    RETURN(Success);
}

#line 347 "unify.nw"
static
FUNCTION(unify_args)
{
    Node *susp, *arglist;

 ENTRY_LABEL(unify_args)
    CHECK_STACK(6);
    CHECK_HEAP(queueMe_node_size);

    arglist = sp[0];
    ASSERT(arglist->info == &pair_cons_info);

    if ( arglist->c.args[2] == nil )
    {
	sp   -= 1;
	sp[0] = arglist->c.args[0];
	sp[1] = arglist->c.args[1];
	GOTO(___61__58__61_);
    }

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
    sp[4] = (Node *)unify_args_1;
    sp[5] = susp;
    sp[6] = arglist->c.args[2];
    start_thread(5);
    GOTO(___61__58__61_);
}

static
FUNCTION(unify_args_1)
{
    Node *r;

 ENTRY_LABEL(unify_args_1)
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
	sp[1] = (Node *)unify_args_2;
	sp[2] = r;
    }
    GOTO(unify_args);
}

static
FUNCTION(unify_args_2)
{
    Node *r;

 ENTRY_LABEL(unify_args_2)
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

#line 446 "unify.nw"
#if !NO_OCCURS_CHECK
boolean
occurs(Node *var, Node *arg)
{
    boolean  is_vect;
    unsigned i, argc;
    Node     **argp;

    while ( is_boxed(arg) && node_tag(arg) == INDIR_TAG )
	arg = arg->n.node;
    if ( is_boxed(arg) )
    {
	if ( arg == var )
	    return true;
	if ( is_constr_node(arg) || is_papp_node(arg) )
	{
	    is_vect = is_vector(arg);
	    argc    = is_vect ? vector_argc(arg) : constr_argc(arg);
	    argp    = is_vect ? arg->a.args : arg->c.args;

	    for ( i = 0; i < argc; i++ )
		if ( occurs(var, argp[i]) )
		    return true;
	}
    }
    return false;
}
#endif /* !NO_OCCURS_CHECK */

static
FUNCTION(unify_var)
{
    boolean	 is_vect;
    unsigned int i, n, sz;
    Node	 *var, *arg, *next, *arglist, **argp;
    Label	 ret_ip;

 ENTRY_LABEL(unify_var)
    if ( !is_local_space(sp[0]->v.spc) )
    {
	if ( is_boxed(sp[1]) && is_variable_node(sp[1])
	     && is_local_space(sp[1]->v.spc) )
	{
	    next  = sp[0];
	    sp[0] = sp[1];
	    sp[1] = next;
	}
	else
	    GOTO(delay_thread(___61__58__61__1, sp[0]));
    }

    var = sp[0];
    arg = sp[1];
    if ( occurs(var, arg) )
	FAIL();

    arglist = nil;
    if ( is_boxed(arg) && (is_constr_node(arg) || is_papp_node(arg)) )
    {
	is_vect = is_vector(arg);
	n	= is_vect ? vector_argc(arg) : constr_argc(arg);

	if ( n > 0 )
	{
	    sz = is_vect ? vector_node_size(n) : constr_node_size(n);
	    CHECK_HEAP(sz + n * (variable_node_size + pair_cons_node_size));
	    memcpy(hp, sp[1], sz * word_size);
	    sp[1] = (Node *)hp;
	    hp	 += sz;

	    argp  = is_vect ? sp[1]->a.args : sp[1]->c.args;
	    argp += n;
	    for ( i = n; i-- > 0; )
	    {
		arg = *--argp;
		while ( is_boxed(arg) && is_indir_node(arg) )
		    arg = arg->n.node;
		/* Hack alert: Checking for !is_int_node(arg) first ensures
		 * that the remaining tests are applied to boxed nodes only */
		/* XXX avoid redundant unification of empty vectors */
		if ( !is_int_node(arg) && !is_float_node(arg)
		     && !is_variable_node(arg)
		     && !(is_constr_node(arg) && constr_argc(arg) == 0)
		     && !(is_papp_node(arg) && closure_argc(arg) == 0)
		     && !is_search_cont_node(arg)
		     && !is_abstract_node(arg) )
		{
		    var	= *argp	    = (Node *)hp;
		    var->v.info	    = &variable_info;
		    var->v.cstrs    = (Constraint *)0;
		    var->v.wq	    = (ThreadQueue)0;
		    var->v.spc	    = ss;
		    hp		   += variable_node_size;
		    next	    = (Node *)hp;
		    next->c.info    = &pair_cons_info;
		    next->c.args[0] = var;
		    next->c.args[1] = arg;
		    next->c.args[2] = arglist;
		    arglist	    = next;
		    hp		   += pair_cons_node_size;
		}
		else
		    *argp = arg;
	    }
	}
    }

    /* bind the variable */
    var = sp[0];
    arg = sp[1];
    if ( arglist == nil )
    {
	sp    += 2;
	ret_ip = (Label)sp[0];
	sp[0]  = Success;
	GOTO(bind_var(var, arg, ret_ip));
    }
    *++sp = arglist;
    GOTO(bind_var(var, arg, unify_args));
}

#line 600 "unify.nw"
DECLARE_LABEL(check_constraints);
DECLARE_LABEL(check_constraints_1);
DECLARE_LABEL(wake);
DECLARE_LABEL(resume_bind);
DECLARE_LABEL(bind_var_1);

Label
bind_var(Node *var, Node *node, Label cont)
{
    boolean	is_var;
    Constraint	*cstrs;
    ThreadQueue	wq;

    if ( !is_boxed(var) || !is_variable_node(var)
	 || !is_local_space(var->v.spc) )
    {
	CHECK_STACK(4);
	sp   -= 4;
	sp[0] = var;
	sp[1] = node;
	sp[2] = (Node *)bind_var_1;
	sp[3] = (Node *)cont;
	return ___61__58__61_;
    }

    cstrs  = var->v.cstrs;
    wq	   = var->v.wq;
    is_var = false;
    for (;;)
    {
	if ( is_boxed(node) )
	    switch ( node->info->tag )
	    {
	    case INDIR_TAG:
		node = node->n.node;
		continue;
	    case VARIABLE_TAG:
		if ( !is_local_space(node->v.spc)
		     && (wq != (ThreadQueue)0 || cstrs != (Constraint *)0) )
		{
		    CHECK_STACK(3);
		    sp	-= 3;
		    sp[0] = var;
		    sp[1] = node;
		    sp[2] = (Node *)cont;
		    return delay_thread(resume_bind, node);
		}
		is_var = true;
		break;
	    }
	break;
    }

    /* update the variable */
    TRACE(("%I %N = %N\n", var, node));
    SAVE(var, v.cstrs);
    SAVE(var, v.wq);
    var->v.cstrs = (Constraint *)0;
    var->v.wq	 = (ThreadQueue)0;
    var->info	 = &variable_indir_info;
    var->n.node  = node;

    /* handle the waitqueue of the variable */
    if ( wq != (ThreadQueue)0 )
    {
	if ( is_var )
	{
	    SAVE(node, v.wq);
	    node->v.wq = join_queues(wq, node->v.wq);
	}
	else
	{
	    CHECK_STACK(2);
	    sp   -= 2;
	    sp[0] = (Node *)wq;
	    sp[1] = (Node *)cont;
	    cont  = wake;
	}
    }

    /* if there are any constraints on the variable re-check them */
    if ( cstrs != (Constraint *)0 )
    {
        CHECK_STACK(3);
	sp   -= 3;
        sp[0] = (Node *)cstrs;
        sp[1] = node;
	sp[2] = (Node *)cont;
        cont  = check_constraints;
    }

    /* we need to check the constraints of the other variable, too */
    if ( is_var && is_local_space(node->v.spc)
	 && node->v.cstrs != (Constraint *)0 )
    {
        CHECK_STACK(3);
	sp   -= 3;
        sp[0] = (Node *)node->v.cstrs;
        sp[1] = node;
	sp[2] = (Node *)cont;
        cont  = check_constraints;
	SAVE(node, v.cstrs);
	node->v.cstrs = (Constraint *)0;
    }

    /* continue evaluation */
    return cont;
}

static
FUNCTION(bind_var_1)
{
    Label cont;

 ENTRY_LABEL(bind_var_1)
    cont = (Label)sp[1];
    sp	+= 2;
    GOTO(cont);
}

static
FUNCTION(resume_bind)
{
    Node  *var, *node;
    Label cont;

 ENTRY_LABEL(resume_bind)
    var	 = sp[0];
    node = sp[1];
    cont = (Label)sp[2];
    sp  += 3;
    GOTO(bind_var(var, node, cont));
}

static
FUNCTION(check_constraints)
{
    Node       *node;
    Constraint *cstrs;

 ENTRY_LABEL(check_constraints)
    cstrs = (Constraint *)sp[0];
    node  = sp[1];
    ASSERT(cstrs != (Constraint *)0);

    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = node;
    sp[1] = (Node *)cstrs;
    sp[2] = (Node *)check_constraints_1;
    sp[3] = (Node *)cstrs->cstrs;
    GOTO(cstrs->info->eval);
}

static
FUNCTION(check_constraints_1)
{
    Constraint *cstrs;
    Label      ret_ip;

 ENTRY_LABEL(check_constraints_1)
    /* XXX check for suspended constraints? */
    cstrs = (Constraint *)sp[1];
    if ( cstrs != (Constraint *)0 )
    {
	sp += 1;
	GOTO(check_constraints);
    }

    ret_ip = (Label)sp[3];
    sp	  += 4;
    GOTO(ret_ip);
}

static
FUNCTION(wake)
{
    Label	ret_ip;
    ThreadQueue	wq;

 ENTRY_LABEL(wake)
    /* handle the waitqueue of the variable */
    wq	   = (ThreadQueue)sp[0];
    ret_ip = (Label)sp[1];
    sp	  += 2;

    /* wake all threads from the queue */
    GOTO(activate_threads(wq, ret_ip));
}
