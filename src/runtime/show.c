#line 17 "show.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "spaces.h"
#include "trail.h"
#include "eval.h"
#include "vars.h"
#include "char.h"
#include "cstring.h"
#include "cam.h"
#include "trace.h"

DECLARE_ENTRYPOINT(__show);
DECLARE_ENTRYPOINT(__dval);
DECLARE_LABEL(showp);
DECLARE_LABEL(showp_eval);
DECLARE_LABEL(showp_lazy);
DECLARE_LABEL(showp_1);
DECLARE_LABEL(showArgs);
DECLARE_LABEL(showArgs_eval);
DECLARE_LABEL(showArgs_lazy);
DECLARE_LABEL(showInfix);
DECLARE_LABEL(showTuple);
DECLARE_LABEL(showTupleArgs);
DECLARE_LABEL(showTupleArgs_eval);
DECLARE_LABEL(showTupleArgs_lazy);
DECLARE_LABEL(showList);
DECLARE_LABEL(showTail);
DECLARE_LABEL(showTail_eval);
DECLARE_LABEL(showTail_lazy);
DECLARE_LABEL(showTail_1);
DECLARE_LABEL(showString);
DECLARE_LABEL(showStringTail);
DECLARE_LABEL(showStringTail_eval);
DECLARE_LABEL(showStringTail_lazy);

#if ONLY_BOXED_OBJECTS
static struct int_node zero_node = { &int_info, 0 };
static struct int_node one_node	 = { &int_info, 1 };
static struct int_node two_node	 = { &int_info, 2 };

# define zero (Node *)&zero_node
# define one  (Node *)&one_node
# define two  (Node *)&two_node
#else
# define zero mk_int(0)
# define one  mk_int(1)
# define two  mk_int(2)
#endif

#define space	 (Node *)(char_table + ' ')
#define comma	 (Node *)(char_table + ',')
#define lparen	 (Node *)(char_table + '(')
#define rparen	 (Node *)(char_table + ')')
#define lbracket (Node *)(char_table + '[')
#define rbracket (Node *)(char_table + ']')
#define bar	 (Node *)(char_table + '|')
#define dblquote (Node *)(char_table + '\"')

static FunctionInfo showp_info = FUNINFO("showp", showp, 4);
static FunctionInfo showArgs_info = FUNINFO("showArgs", showArgs, 4);
static FunctionInfo showTupleArgs_info = 
    FUNINFO("showTupleArgs", showTupleArgs, 3);
static FunctionInfo showTail_info = FUNINFO("showTail", showTail, 3);
static FunctionInfo showStringTail_info =
    FUNINFO("showStringTail", showStringTail, 2);

static NodeInfo showp_suspend_info = SUSPINFO(showp);
static NodeInfo showArgs_suspend_info = SUSPINFO(showArgs);
static NodeInfo showTupleArgs_suspend_info = SUSPINFO(showTupleArgs);
static NodeInfo showTail_suspend_info = SUSPINFO(showTail);
static NodeInfo showStringTail_suspend_info = SUSPINFO(showStringTail);

#line 107 "show.nw"
FUNCTION(__show)
{
    EXPORT_LABEL(__show)
 ENTRY_LABEL(__show)
    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = sp[3];
    sp[1] = zero;
    sp[2] = nil;
    sp[3] = one;
    GOTO(showp);
}

FUNCTION(__dval)
{
    EXPORT_LABEL(__dval)
 ENTRY_LABEL(__dval)
    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = sp[3];
    sp[1] = zero;
    sp[2] = nil;
    sp[3] = zero;
    GOTO(showp);
}

#line 141 "show.nw"
static
FUNCTION(showp_eval)
{
    Node *clos;
 ENTRY_LABEL(showp_eval)
    CHECK_STACK(3);
    clos  = sp[0];
    sp	 -= 3;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    sp[3] = clos->cl.args[3];
    GOTO(showp);
}

static
FUNCTION(showp_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(showp_lazy)
    susp = sp[0];

    /* suspend the search if the node is not local */
    if ( !is_local_space(susp->s.spc) )
	GOTO(suspend_thread(resume, susp));

    /* lock the suspension */
    clos = susp->s.fn;
    SAVE(susp, q.wq);
    susp->info = &queueMe_info;
    susp->q.wq = (ThreadQueue)0;

    /* create an update frame */
    CHECK_STACK(5);
    sp   -= 5;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    sp[3] = clos->cl.args[3];
    sp[4] = (Node *)update;

    /* enter the callee */
    GOTO(showp);
}

static
FUNCTION(showp)
{
 ENTRY_LABEL(showp)
    TRACE(("%I enter showp%V\n", 4, sp));
    GOTO(showp_1);
}

static
FUNCTION(showp_1)
{
    boolean	 isop;
    boolean	 isneg;
    char	 buf[32], *cp;
    const char   *str;
    unsigned int i, argc;
    double	 d;
    Node	 *node, *clos, *cons, *tail, *arglist, **argp, *prec, *show;

 ENTRY_LABEL(showp_1)

    str	  = buf;
    argc  = 0;
    node  = sp[0];
    show  = sp[3];
    isop  = false;
    isneg = false;

 again:
#if !ONLY_BOXED_OBJECTS
    if ( is_unboxed(node) )
    {
	sprintf(buf, "%ld", unboxed_val(node));
	isneg = buf[0] == '-';
    }
    else
#endif
	switch ( node_tag(node) )
	{
	case INDIR_TAG:
	    node = node->n.node;
	    goto again;

	case CLOSURE_TAG:
	case SUSPEND_TAG:
	case QUEUEME_TAG:
	    if ( show != zero )
	    {
		CHECK_STACK1();
		sp   -= 1;
		sp[0] = node;
		sp[1] = (Node *)showp_1;
		GOTO(node->info->eval);
	    }
	    str = "_";
	    break;

	case VARIABLE_TAG:
	    if ( show != zero )
	    {
		sp[0] = node;
		GOTO(delay_thread(showp_1, node));
	    }
	    str = lookup_name(node);
	    break;

	case CHAR_TAG:
	    sprintf(buf, "'%s'", lit_char(node->ch.ch, '\''));
	    break;

#if ONLY_BOXED_OBJECTS
	case INT_TAG:
	    sprintf(buf, "%ld", node->i.i);
	    isneg = buf[0] == '-';
	    break;
#endif

	case FLOAT_TAG:
	    get_float_val(d, node->f);
	    sprintf(buf, "%g", d);

	    cp = strpbrk(buf, ".e");
	    if ( cp == (char *)0 )
		strcat(buf, ".0");
	    else if ( *cp != '.'  )
	    {
		i = strlen(cp) + 1;
		for ( cp += i; i-- > 0; cp-- )
		    cp[2] = cp[0];
		cp[1] = '.';
		cp[2] = '0';
	    }
	    isneg = buf[0] == '-';
	    break;

	case PAPP_TAG:
	    argc = closure_argc(node);
	    str  = node->info->cname;
	    isop = is_operator(node->info);
	    break;

	case SEARCH_CONT_TAG:
	    str = node->info->cname;
	    break;

	default:
	    ASSERT(is_constr_node(node) || is_abstract_node(node));
	    if ( is_abstract_node(node) )
	    {
		str = node->info->cname;
		if ( str == (const char *)0 )
		    str = "<abstract>";
	    }
	    else if ( node->info == (NodeInfo *)&cons_info )
	    {
		sp[0] = node->c.args[0];
		sp[1] = node->c.args[1];
		GOTO(showList);
	    }
	    else if ( is_tuple(node->info) )
	    {
		*++sp = node;
		GOTO(showTuple);
	    }
	    else
	    {
		str  = node->info->cname;
		argc = is_vector(node) ? vector_argc(node)
			               : constr_argc(node);
	    }
	    isop = node->info->cname && is_operator(node->info);
	}

    if ( isop && argc == 2 )
    {
	sp[0] = node;
	GOTO(showInfix);
    }

    sp[0] = node;
    CHECK_HEAP((argc + 1) * cons_node_size + closure_node_size(4)
	       + suspend_node_size);
    node = sp[0];
    prec = sp[1];
    tail = sp[2];
    show = sp[3];

    if ( argc > 0 )
    {
	if ( is_papp_node(node) )
	    argp = node->cl.args;
	else if ( is_vector(node) )
	    argp = node->a.args;
	else
	    argp = node->c.args;

	arglist = nil;
	for ( i = argc; i-- > 0; )
	{
	    cons	    = (Node *)hp;
	    cons->c.info    = &cons_info;
	    cons->c.args[0] = argp[i];
	    cons->c.args[1] = arglist;
	    arglist	    = cons;
	    hp		   += cons_node_size;
	}

	clos		 = (Node *)hp;
	clos->cl.info    = &showArgs_info;
	clos->cl.args[0] = arglist;
	clos->cl.args[1] = prec;
	clos->cl.args[2] = tail;
	clos->cl.args[3] = show;
	hp		+= closure_node_size(4);

	tail	     = (Node *)hp;
	tail->s.info = &showArgs_suspend_info;
	tail->s.fn   = clos;
	tail->s.spc  = ss;
	hp	    += suspend_node_size;
    }

    if ( isop || (isneg && int_val(prec) > 0) )
    {
	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = rparen;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;

	tail = cons;
    }

    sp[0] = prefix_string(str, tail);

    CHECK_HEAP(2*cons_node_size);
    cons = sp[0];
    prec = sp[1];
    sp  += 4;
    if ( isop || (isneg && int_val(prec) > 0) )
    {
	tail		= cons;
	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = lparen;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;
    }
    if ( int_val(prec) > 1 && argc > 0 )
    {
	tail		= cons;
	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = lparen;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;
    }

    RETURN(cons);
}

#line 413 "show.nw"
static
FUNCTION(showArgs_eval)
{
    Node *clos;
 ENTRY_LABEL(showArgs_eval)
    CHECK_STACK(3);
    clos  = sp[0];
    sp	 -= 3;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    sp[3] = clos->cl.args[3];
    GOTO(showArgs);
}

static
FUNCTION(showArgs_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(showArgs_lazy)
    susp = sp[0];

    /* suspend the search if the node is not local */
    if ( !is_local_space(susp->s.spc) )
	GOTO(suspend_thread(resume, susp));

    /* lock the suspension */
    clos = susp->s.fn;
    SAVE(susp, q.wq);
    susp->info = &queueMe_info;
    susp->q.wq = (ThreadQueue)0;

    /* create an update frame */
    CHECK_STACK(5);
    sp   -= 5;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    sp[3] = clos->cl.args[3];
    sp[4] = (Node *)update;

    /* enter the callee */
    GOTO(showArgs);
}

static
FUNCTION(showArgs)
{
    Node *arglist, *clos, *susp, *cons, *tail, *prec, *show;

 ENTRY_LABEL(showArgs)
    TRACE(("%I enter showArgs%V\n", 4, sp));
    CHECK_HEAP(2 * (closure_node_size(4) + suspend_node_size)
	       + cons_node_size);
    arglist = sp[0];
    prec    = sp[1];
    tail    = sp[2];
    show    = sp[3];
    sp	   += 4;

    if ( arglist->info->tag == NIL_TAG )
    {
	if ( int_val(prec) > 1 )
	{
	    cons	    = (Node *)hp;
	    cons->c.info    = &cons_info;
	    cons->c.args[0] = rparen;
	    cons->c.args[1] = tail;
	    hp		   += cons_node_size;
	}
	else
	{
	    *--sp = tail;
	    GOTO(tail->info->eval);
	}
    }
    else
    {
	ASSERT(arglist->info->tag == CONS_TAG);

	clos		 = (Node *)hp;
	clos->cl.info	 = &showArgs_info;
	clos->cl.args[0] = arglist->c.args[1];
	clos->cl.args[1] = prec;
	clos->cl.args[2] = tail;
	clos->cl.args[3] = show;
	hp		+= closure_node_size(4);

	susp	     = (Node *)hp;
	susp->s.info = &showArgs_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	clos		 = (Node *)hp;
	clos->cl.info	 = &showp_info;
	clos->cl.args[0] = arglist->c.args[0];
	clos->cl.args[1] = two;
	clos->cl.args[2] = susp;
	clos->cl.args[3] = show;
	hp		+= closure_node_size(4);

	susp	     = (Node *)hp;
	susp->s.info = &showp_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	cons		= (Node *)hp;
	cons->c.info	= &cons_info;
	cons->c.args[0] = space;
	cons->c.args[1] = susp;
	hp	       += cons_node_size;
    }

    RETURN(cons);
}

#line 539 "show.nw"
static
FUNCTION(showInfix)
{
    int prec;
    Node *node, *tail, *show, *cons, *clos, *susp;
 ENTRY_LABEL(showInfix)

    CHECK_HEAP(2 * cons_node_size + closure_node_size(4) + suspend_node_size);
    node = sp[0];
    prec = int_val(sp[1]);
    tail = sp[2];
    show = sp[3];

    if ( prec > 0 )
    {
	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = rparen;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;

	tail = cons;
    }

    clos	     = (Node *)hp;
    clos->cl.info    = &showp_info;
    clos->cl.args[0] = node->c.args[1];
    clos->cl.args[1] = one;
    clos->cl.args[2] = tail;
    clos->cl.args[3] = show;
    hp		    += closure_node_size(4);

    susp	 = (Node *)hp;
    susp->s.info = &showp_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc  = ss;
    hp		+= suspend_node_size;

    cons	    = (Node *)hp;
    cons->c.info    = &cons_info;
    cons->c.args[0] = space;
    cons->c.args[1] = susp;
    hp		   += cons_node_size;

    sp[0] = node->c.args[0];
    sp[2] = prefix_string(node->info->cname, cons);

    CHECK_HEAP(2 * cons_node_size + closure_node_size(4) + suspend_node_size);
    node = sp[0];
    tail = sp[2];
    show = sp[3];
    sp	+= 4;

    cons	    = (Node *)hp;
    cons->c.info    = &cons_info;
    cons->c.args[0] = space;
    cons->c.args[1] = tail;
    hp		   += cons_node_size;

    clos	     = (Node *)hp;
    clos->cl.info    = &showp_info;
    clos->cl.args[0] = node;
    clos->cl.args[1] = one;
    clos->cl.args[2] = cons;
    clos->cl.args[3] = show;
    hp		    += closure_node_size(4);

    susp	 = (Node *)hp;
    susp->s.info = &showp_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc  = ss;
    hp		+= suspend_node_size;

    if ( prec > 0 )
    {
	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = lparen;
	cons->c.args[1] = susp;
	hp	       += cons_node_size;
    }
    else
	cons = susp;

    RETURN(cons);
}

#line 635 "show.nw"
static
FUNCTION(showTuple)
{
    unsigned int i, argc;
    Node	 *tuple, *clos, *susp, *cons, *tail, *arglist, **argp, *show;

 ENTRY_LABEL(showTuple)

    argc = is_vector(sp[0]) ? vector_argc(sp[0]) : constr_argc(sp[0]);
    CHECK_HEAP(argc * cons_node_size + closure_node_size(3)
	       + closure_node_size(4) + 2*suspend_node_size);
    tuple = sp[0];
    tail  = sp[1];
    show  = sp[2];
    sp	 += 3;

    argp    = is_vector(tuple) ? tuple->a.args : tuple->c.args;
    argp   += argc;
    arglist = nil;
    for ( i = argc; i-- > 1; )
    {
	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = *--argp;
	cons->c.args[1] = arglist;
	arglist		= cons;
	hp	       += cons_node_size;
    }

    clos	     = (Node *)hp;
    clos->cl.info    = &showTupleArgs_info;
    clos->cl.args[0] = arglist;
    clos->cl.args[1] = tail;
    clos->cl.args[2] = show;
    hp		    += closure_node_size(3);

    susp	 = (Node *)hp;
    susp->s.info = &showTupleArgs_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc	 = ss;
    hp		+= suspend_node_size;

    clos	     = (Node *)hp;
    clos->cl.info    = &showp_info;
    clos->cl.args[0] = *--argp;
    clos->cl.args[1] = zero;
    clos->cl.args[2] = susp;
    clos->cl.args[3] = show;
    hp		    += closure_node_size(4);

    susp	 = (Node *)hp;
    susp->s.info = &showp_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc	 = ss;
    hp		+= suspend_node_size;

    cons	    = (Node *)hp;
    cons->c.info    = &cons_info;
    cons->c.args[0] = lparen;
    cons->c.args[1] = susp;
    hp		   += cons_node_size;

    RETURN(cons);
}

static
FUNCTION(showTupleArgs_eval)
{
    Node *clos;
 ENTRY_LABEL(showTupleArgs_eval)
    CHECK_STACK(2);
    clos  = sp[0];
    sp	 -= 2;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    GOTO(showTupleArgs);
}

static
FUNCTION(showTupleArgs_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(showTupleArgs_lazy)
    susp = sp[0];

    /* suspend the search if the node is not local */
    if ( !is_local_space(susp->s.spc) )
	GOTO(suspend_thread(resume, susp));

    /* lock the suspension */
    clos = susp->s.fn;
    SAVE(susp, q.wq);
    susp->info = &queueMe_info;
    susp->q.wq = (ThreadQueue)0;

    /* create an update frame */
    CHECK_STACK(4);
    sp   -= 4;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    sp[3] = (Node *)update;

    /* enter the callee */
    GOTO(showTupleArgs);
}

static
FUNCTION(showTupleArgs)
{
    Node *arglist, *clos, *susp, *cons, *tail, *show;

 ENTRY_LABEL(showTupleArgs)
    TRACE(("%I enter showTupleArgs%V\n", 3, sp));
    CHECK_HEAP(closure_node_size(3) + closure_node_size(4)
	       + 2*suspend_node_size + cons_node_size);
    arglist = sp[0];
    tail    = sp[1];
    show    = sp[2];
    sp	   += 3;

    if ( arglist->info->tag == NIL_TAG )
    {
	cons		= (Node *)hp;
	cons->c.info	= &cons_info;
	cons->c.args[0] = rparen;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;
    }
    else
    {
	ASSERT(arglist->info->tag == CONS_TAG);

	clos		 = (Node *)hp;
	clos->cl.info	 = &showTupleArgs_info;
	clos->cl.args[0] = arglist->c.args[1];
	clos->cl.args[1] = tail;
	clos->cl.args[2] = show;
	hp		+= closure_node_size(3);

	susp	     = (Node *)hp;
	susp->s.info = &showTupleArgs_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	clos		 = (Node *)hp;
	clos->cl.info	 = &showp_info;
	clos->cl.args[0] = arglist->c.args[0];
	clos->cl.args[1] = zero;
	clos->cl.args[2] = susp;
	clos->cl.args[3] = show;
	hp		+= closure_node_size(4);

	susp	     = (Node *)hp;
	susp->s.info = &showp_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	cons		= (Node *)hp;
	cons->c.info	= &cons_info;
	cons->c.args[0] = comma;
	cons->c.args[1] = susp;
	hp	       += cons_node_size;
    }

    RETURN(cons);
}

#line 832 "show.nw"
static
FUNCTION(showList)
{
    Node *hd, *tl, *clos, *susp, *cons, *tail, *show;

 ENTRY_LABEL(showList)
    hd = sp[0];
    show = sp[3];
    if ( show != zero )
    {
    again:
	if ( is_boxed(hd) )
	    switch ( hd->info->tag )
	    {
	    case INDIR_TAG:
		hd = hd->n.node;
		goto again;
	    case SUSPEND_TAG:
	    case QUEUEME_TAG:
	    case CLOSURE_TAG:
		CHECK_STACK1();
		sp -= 1;
		sp[0] = hd;
		sp[1] = (Node *)showList;
		GOTO(hd->info->eval);
	    case VARIABLE_TAG:
		sp[0] = hd;
		GOTO(delay_thread(showList, hd));
	    case CHAR_TAG:
		sp[0] = hd;
		CHECK_HEAP(closure_node_size(2) + suspend_node_size
			   + 2*cons_node_size);

		hd   = sp[0];
		tl   = sp[1];
		tail = sp[2];
		sp  += 4;

		cons = (Node *)hp;
		cons->c.info = &cons_info;
		cons->c.args[0] = hd;
		cons->c.args[1] = tl;
		hp	       += cons_node_size;

		clos		 = (Node *)hp;
		clos->cl.info	 = &showStringTail_info;
		clos->cl.args[0] = cons;
		clos->cl.args[1] = tail;
		hp		+= closure_node_size(2);

		susp	     = (Node *)hp;
		susp->s.info = &showStringTail_suspend_info;
		susp->s.fn   = clos;
		susp->s.spc  = ss;
		hp	    += suspend_node_size;

		cons		= (Node *)hp;
		cons->c.info	= &cons_info;
		cons->c.args[0] = dblquote;
		cons->c.args[1] = susp;
		hp	       += cons_node_size;

		RETURN(cons);
	    }
	sp[0] = hd;
    }

    CHECK_HEAP(closure_node_size(3) + closure_node_size(4)
	       + 2*suspend_node_size + cons_node_size);
    hd   = sp[0];
    tl	 = sp[1];
    tail = sp[2];
    show = sp[3];
    sp	+= 4;

    clos	     = (Node *)hp;
    clos->cl.info    = &showTail_info;
    clos->cl.args[0] = tl;
    clos->cl.args[1] = tail;
    clos->cl.args[2] = show;
    hp		    += closure_node_size(3);

    susp	 = (Node *)hp;
    susp->s.info = &showTail_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc	 = ss;
    hp		+= suspend_node_size;

    clos	     = (Node *)hp;
    clos->cl.info    = &showp_info;
    clos->cl.args[0] = hd;
    clos->cl.args[1] = zero;
    clos->cl.args[2] = susp;
    clos->cl.args[3] = show;
    hp		    += closure_node_size(4);

    susp	 = (Node *)hp;
    susp->s.info = &showp_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc	 = ss;
    hp		+= suspend_node_size;

    cons	    = (Node *)hp;
    cons->c.info    = &cons_info;
    cons->c.args[0] = lbracket;
    cons->c.args[1] = susp;
    hp		   += cons_node_size;

    RETURN(cons);
}

static
FUNCTION(showTail_eval)
{
    Node *clos;
 ENTRY_LABEL(showTail_eval)
    CHECK_STACK(2);
    clos  = sp[0];
    sp	 -= 2;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    GOTO(showTail);
}

static
FUNCTION(showTail_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(showTail_lazy)
    susp = sp[0];

    /* suspend the search if the node is not local */
    if ( !is_local_space(susp->s.spc) )
	GOTO(suspend_thread(resume, susp));

    /* lock the suspension */
    clos = susp->s.fn;
    SAVE(susp, q.wq);
    susp->info = &queueMe_info;
    susp->q.wq = (ThreadQueue)0;

    /* create an update frame */
    CHECK_STACK(4);
    sp   -= 4;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = clos->cl.args[2];
    sp[3] = (Node *)update;

    /* enter the callee */
    GOTO(showTail);
}

static
FUNCTION(showTail)
{
 ENTRY_LABEL(showTail)
    TRACE(("%I enter showTail%V\n", 3, sp));
    GOTO(showTail_1);
}

static
FUNCTION(showTail_1)
{
    Node *list, *clos, *susp, *cons, *tail, *show;

 ENTRY_LABEL(showTail_1)
    list = sp[0];
    show = sp[2];
 again:
    switch ( node_tag(list) )
    {
    case INDIR_TAG:
	list = list->n.node;
	goto again;

    case CLOSURE_TAG:
    case SUSPEND_TAG:
    case QUEUEME_TAG:
	if ( show != zero )
	{
	    CHECK_STACK1();
	    sp -= 1;
	    sp[0] = list;
	    sp[1] = (Node *)showTail_1;
	    GOTO(list->info->eval);
	}
	goto make_tail;

    case VARIABLE_TAG:
	if ( show != zero )
	{
	    sp[0] = list;
	    GOTO(delay_thread(showTail_1, list));
	}
    make_tail:
	sp[0] = list;
	CHECK_HEAP(closure_node_size(4) + suspend_node_size
		   + 2*cons_node_size);
	list = sp[0];
	tail = sp[1];
	show = sp[2];
	sp  += 3;

	cons		= (Node *)hp;
	cons->c.info	= &cons_info;
	cons->c.args[0] = rbracket;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;

	clos		 = (Node *)hp;
	clos->cl.info    = &showp_info;
	clos->cl.args[0] = list;
	clos->cl.args[1] = zero;
	clos->cl.args[2] = cons;
	clos->cl.args[3] = show;
	hp		+= closure_node_size(4);

	susp	     = (Node *)hp;
	susp->s.info = &showp_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = bar;
	cons->c.args[1] = susp;
	hp	       += cons_node_size;
	break;

    case NIL_TAG:
	CHECK_HEAP(cons_node_size);
	tail = sp[1];
	sp  += 3;

	cons		= (Node *)hp;
	cons->c.info	= &cons_info;
	cons->c.args[0] = rbracket;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;
	break;

    case CONS_TAG:
	sp[0] = list;
	CHECK_HEAP(closure_node_size(3) + closure_node_size(4)
		   + 2*suspend_node_size + cons_node_size);
	list = sp[0];
	tail = sp[1];
	show = sp[2];
	sp  += 3;

	clos		 = (Node *)hp;
	clos->cl.info    = &showTail_info;
	clos->cl.args[0] = list->c.args[1];
	clos->cl.args[1] = tail;
	clos->cl.args[2] = show;
	hp		+= closure_node_size(3);

	susp	     = (Node *)hp;
	susp->s.info = &showTail_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	clos		 = (Node *)hp;
	clos->cl.info    = &showp_info;
	clos->cl.args[0] = list->c.args[0];
	clos->cl.args[1] = zero;
	clos->cl.args[2] = susp;
	clos->cl.args[3] = show;
	hp		+= closure_node_size(4);

	susp	     = (Node *)hp;
	susp->s.info = &showp_suspend_info;
	susp->s.fn   = clos;
	susp->s.spc  = ss;
	hp	    += suspend_node_size;

	cons		= (Node *)hp;
	cons->c.info    = &cons_info;
	cons->c.args[0] = comma;
	cons->c.args[1] = susp;
	hp	       += cons_node_size;
	break;

    default:
	fprintf(stderr, "Bad list tail in showTail\n");
	exit(1);
    }

    RETURN(cons);
}

#line 1133 "show.nw"
static
FUNCTION(showString)
{
    Node *hd, *tl, *tail, *clos, *susp, *cons;

 ENTRY_LABEL(showString);
    EVAL_RIGID_CHAR(showString);
    CHECK_HEAP(closure_node_size(2) + suspend_node_size);

    hd	 = sp[0];
    tl	 = sp[1];
    tail = sp[2];
    sp	+= 3;

    clos	     = (Node *)hp;
    clos->cl.info    = &showStringTail_info;
    clos->cl.args[0] = tl;
    clos->cl.args[1] = tail;
    hp		    += closure_node_size(2);

    susp	 = (Node *)hp;
    susp->s.info = &showStringTail_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc	 = ss;
    hp		+= suspend_node_size;

    cons = prefix_string(lit_char(hd->ch.ch, '"'), susp);
    RETURN(cons);
}

static
FUNCTION(showStringTail_eval)
{
    Node *clos;
 ENTRY_LABEL(showStringTail_eval)
    CHECK_STACK(1);
    clos  = sp[0];
    sp	 -= 1;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    GOTO(showStringTail);
}

static
FUNCTION(showStringTail_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(showStringTail_lazy)
    susp = sp[0];

    /* suspend the search if the node is not local */
    if ( !is_local_space(susp->s.spc) )
	GOTO(suspend_thread(resume, susp));

    /* lock the suspension */
    clos = susp->s.fn;
    SAVE(susp, q.wq);
    susp->info = &queueMe_info;
    susp->q.wq = (ThreadQueue)0;

    /* create an update frame */
    CHECK_STACK(3);
    sp   -= 3;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = (Node *)update;

    /* enter the callee */
    GOTO(showStringTail);
}

static
FUNCTION(showStringTail)
{
    Node *cons;

 ENTRY_LABEL(showStringTail)
    EVAL_RIGID_POLY(showStringTail);

    if ( sp[0] == nil )
    {
	CHECK_HEAP(cons_node_size);

	cons		= (Node *)hp;
	cons->c.info	= &cons_info;
	cons->c.args[0] = dblquote;
	cons->c.args[1] = sp[1];
	hp	       += cons_node_size;

	sp += 2;
	RETURN(cons);
    }

    ASSERT(sp[0]->info == &cons_info);
    CHECK_STACK1();
    sp	 -= 1;
    sp[0] = sp[1]->c.args[0];
    sp[1] = sp[1]->c.args[1];
    GOTO(showString);
}

#line 1243 "show.nw"
DECLARE_ENTRYPOINT(__showEFloat);
DECLARE_ENTRYPOINT(__showFFloat);

DECLARE_LABEL(__showEFloat_1);
DECLARE_LABEL(__showFFloat_1);

FUNCTION(__showEFloat)
{
    Node *p, *d;
    EXPORT_LABEL(__showEFloat)
 ENTRY_LABEL(__showEFloat)
    EVAL_RIGID_INT(__showEFloat);
    p	  = sp[0];
    d	  = sp[1];
    sp[0] = d;
    sp[1] = p;
    GOTO(__showEFloat_1);
}

static
FUNCTION(__showEFloat_1)
{
    int    p, n;
    double d;
    char   fmt[20], *buf;
    Node   *str;
 ENTRY_LABEL(__showEFloat_1)
    EVAL_RIGID_FLOAT(__showEFloat_1);
    get_float_val(d, sp[0]->f);
    p   = int_val(sp[1]);
    str = sp[2];
    if ( p >= 0 )
	sprintf(fmt, "%%.%de", p);
    else
	strcpy(fmt, "%e");
    n   = p >= 0 ? 10 + p : 25;
    buf = (char *)malloc(n);
    if ( buf == (char *)0 )
    {
	fprintf(stderr, "showEFloat: memory exhausted\n");
	exit(1);
    }
    sprintf(buf, fmt, d);

    sp += 3;
    str = prefix_string(buf, str);
    free(buf);
    RETURN(str);
}

FUNCTION(__showFFloat)
{
    Node *p, *d;
    EXPORT_LABEL(__showFFloat)
 ENTRY_LABEL(__showFFloat)
    EVAL_RIGID_INT(__showFFloat);
    p	  = sp[0];
    d	  = sp[1];
    sp[0] = d;
    sp[1] = p;
    GOTO(__showFFloat_1);
}

static
FUNCTION(__showFFloat_1)
{
    int    p, n;
    double d;
    char   fmt[20], *buf;
    Node   *str;
 ENTRY_LABEL(__showFFloat_1)
    EVAL_RIGID_FLOAT(__showFFloat_1);
    get_float_val(d, sp[0]->f);
    p   = int_val(sp[1]);
    str = sp[2];
    if ( p >= 0 )
	sprintf(fmt, "%%.%df", p);
    else
	strcpy(fmt, "%f");
    frexp(d, &n);
    if ( p >= 0 )
	n = (n > 0 ? n / 3 + 4 : 5) + p;
    else
	n = (n >= 0 ? n : -n) / 3 + 20;
    buf = (char *)malloc(n);
    if ( buf == (char *)0 )
    {
	fprintf(stderr, "showFFloat: memory exhausted\n");
	exit(1);
    }
    sprintf(buf, fmt, d);

    sp += 3;
    str = prefix_string(buf, str);
    free(buf);
    RETURN(str);
}
