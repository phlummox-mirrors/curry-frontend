#line 15 "eval.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "trail.h"
#include "threads.h"
#include "spaces.h"
#include "trace.h"
#include "eval.h"
#include "cam.h"

#line 40 "eval.nw"
FUNCTION(no_eval)
{
    EXPORT_LABEL(no_eval)
 ENTRY_LABEL(no_eval)

    fprintf(stderr, "Internal error: this object should not be evaluated\n");
    exit(9);
}

#line 59 "eval.nw"
FUNCTION(eval_whnf)
{
    Node *self;

    EXPORT_LABEL(eval_whnf)
 ENTRY_LABEL(eval_whnf)
    self = *sp++;
    RETURN(self);
}

#line 81 "eval.nw"
FUNCTION(eval_indir)
{
    Node *node;

    EXPORT_LABEL(eval_indir)
 ENTRY_LABEL(eval_indir)

    node = sp[0];
    ASSERT(is_boxed(node) && is_indir_node(node));

    /* dereference the indirection */
    do
    {
        node = node->n.node;
    }
    while ( is_boxed(node) && node->info->tag == INDIR_TAG );

    /* enter the node */
    if ( is_unboxed(node) )
    {
	sp += 1;
        RETURN(node);
    }
    sp[0] = node;
    GOTO(node->info->eval);
}

#line 119 "eval.nw"
FUNCTION(eval_queueMe)
{
    EXPORT_LABEL(eval_queueMe)
 ENTRY_LABEL(eval_queueMe)

    GOTO(suspend_thread(resume, sp[0]));
}

#line 139 "eval.nw"
FUNCTION(update)
{
    Node       *result, *susp;
    Label       ret_ip;
    ThreadQueue wq;

    EXPORT_LABEL(update)
 ENTRY_LABEL(update)

    result = sp[0];
    susp   = sp[1];
    ret_ip = (Label)sp[2];
    sp	  += 2;
    ASSERT(is_boxed(susp) && is_queueMe_node(susp) &&
	   is_local_space(susp->q.spc));

    /* update the suspended application */
    TRACE(("%I %N = %N\n", susp, result));
    wq = susp->q.wq;
    SAVE(susp, q.wq);
    susp->info	 = &suspend_indir_info;
    susp->n.node = result;
    sp[0]	 = result;

    /* wake all threads on the wait-queue of the application */
    if ( wq != (ThreadQueue)0 )
	wake_threads(wq);

    /* return to the caller */
    GOTO(ret_ip);
}

#line 184 "eval.nw"
FUNCTION(resume)
{
    Node  *result;
    Label ret_ip;

    EXPORT_LABEL(resume)
 ENTRY_LABEL(resume)

    /* dereference the indirection */
    result = sp[0];
    ret_ip = (Label)sp[1];
    while ( is_boxed(result) && result->info->tag == INDIR_TAG )
	result = result->n.node;
    *++sp = result;

    /* return to the caller */
    GOTO(ret_ip);
}

#line 231 "eval.nw"
DECLARE_LABEL(___64__eval);
DECLARE_LABEL(___64__lazy);

FunctionInfo ___64__info	 = FUNINFO("@", ___64_, 2);
NodeInfo     ___64__suspend_info = SUSPINFO(___64_);

static
FUNCTION(___64__eval)
{
    Node *clos;
 ENTRY_LABEL(___64__eval)
    CHECK_STACK1();
    clos  = sp[0];
    sp	 -= 1;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    GOTO(___64_);
}

static
FUNCTION(___64__lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(___64__lazy)
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
    GOTO(___64_);
}

DECLARE_LABEL(___64__1);

FUNCTION(___64_)
{
    EXPORT_LABEL(___64_)
 ENTRY_LABEL(___64_)
    TRACE(("%I enter @%V\n", 2, sp));
    GOTO(___64__1);
}

static
FUNCTION(___64__1)
{
    unsigned int argc;
    Node	 *clos;
    FunctionInfo *fInfo;

 ENTRY_LABEL(___64__1)
    /* evaluate the function argument to head normal form */
    EVAL_RIGID(___64__1);
    clos = sp[0];
    ASSERT(is_boxed(clos) && is_papp_node(clos));

    /* check the number of missing arguments */
    fInfo = clos->cl.info;
    argc  = closure_argc(clos);
    ASSERT(fInfo->arity > argc);
    if ( argc + 1 == fInfo->arity )
    {
	ASSERT(fInfo[1].node_info.tag == CLOSURE_TAG);

	/* push the arguments onto the stack */
	CHECK_STACK(argc - 1);
	sp -= argc - 1;
	memcpy(sp, clos->cl.args, argc * word_size);

	/* perform a tail call to the closure */
	GOTO(fInfo->entry);
    }

    /* allocate a new closure for the application */
    CHECK_HEAP(closure_node_size(argc + 1));

    /* create a new closure from the old closure and the argument */
    clos = (Node *)hp;
    memcpy(clos, sp[0], closure_node_size(argc) * word_size);
    clos->cl.info++;
    clos->cl.args[argc] = sp[1];
    hp += closure_node_size(argc + 1);

    /* return to the caller */
    sp += 2;
    RETURN(clos);
}

#line 341 "eval.nw"
DECLARE_LABEL(___58_);
DECLARE_LABEL(___58__eval);
FunctionInfo ___58__info_table[] = {
    PAPPINFO(":", 0, ___58_, 2)
    PAPPINFO(":", 1, ___58_, 2)
    FUNINFO(":",     ___58_, 2)
};
struct closure_node ___58__function = { ___58__info_table, { } };

static
FUNCTION(___58__eval)
{
    Node *clos;
 ENTRY_LABEL(___58__eval)
    CHECK_STACK1();
    clos  = sp[0];
    sp	 -= 1;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    GOTO(___58_);
}

static
FUNCTION(___58_)
{
    Node *cons;

 ENTRY_LABEL(___58_)

    TRACE(("%I enter :%V\n", 2, sp));

    CHECK_HEAP(cons_node_size);
    cons	    = (Node *)hp;
    cons->c.info    = &cons_info;
    cons->c.args[0] = sp[0];
    cons->c.args[1] = sp[1];
    hp		   += cons_node_size;

    sp += 2;
    RETURN(cons);
}

#line 389 "eval.nw"
DECLARE_ENTRYPOINT(__seq);

FUNCTION(__seq)
{
    Node *node;

    EXPORT_LABEL(__seq)
 ENTRY_LABEL(__seq)
    EVAL_RIGID_POLY(__seq);
    node = sp[1];
    if ( is_boxed(node) )
    {
	sp += 1;
	GOTO(node->info->eval);
    }
    sp += 2;
    RETURN(node);
}

#line 413 "eval.nw"
DECLARE_ENTRYPOINT(__failed);

FUNCTION(__failed)
{
    EXPORT_LABEL(__failed)
 ENTRY_LABEL(__failed)
    FAIL();
}

#line 429 "eval.nw"
DECLARE_ENTRYPOINT(__ground);
DECLARE_LABEL(__ground_eval);
DECLARE_LABEL(__ground_lazy);
DECLARE_LABEL(__ground_1);

static
FUNCTION(__ground_eval)
{
    Node *clos;
 ENTRY_LABEL(__ground_eval)
    clos  = sp[0];
    sp[0] = clos->cl.args[0];
    GOTO(__ground);
}

static
FUNCTION(__ground_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(__ground_lazy)
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
    CHECK_STACK(2);
    sp   -= 2;
    sp[0] = clos->cl.args[0];
    sp[1] = (Node *)update;

    /* enter the callee */
    GOTO(__ground);
}

FUNCTION(__ground)
{
    EXPORT_LABEL(__ground)
 ENTRY_LABEL(__ground)
    TRACE(("%I enter ground%V\n", 1, sp));
    GOTO(__ground_1);
}

static
FUNCTION(__ground_1)
{
    boolean		is_vect;
    unsigned int	n, sz;
    Node		*node, **argp, *clos, *susp;
    static FunctionInfo ground_info	    = FUNINFO("ground", __ground, 1);
    static NodeInfo     ground_suspend_info = SUSPINFO(__ground);
 ENTRY_LABEL(__ground_1)
    EVAL_RIGID_POLY(__ground_1);
    node = sp[0];
    if ( is_boxed(node) && (is_constr_node(node) || is_papp_node(node)) )
    {
	is_vect = is_vector(node);
	n	= is_vect ? vector_argc(node) : constr_argc(node);
	if ( n > 0 )
	{
	    sz = is_vect ? vector_node_size(n) : node_size(node);
	    CHECK_HEAP(sz + n * (closure_node_size(1) + suspend_node_size));

	    node = (Node *)(hp + n * (closure_node_size(1) + suspend_node_size));
	    memcpy(node, sp[0], sz * word_size);

	    for ( argp = is_vect ? node->a.args : node->c.args;
		  n > 0; 
		  argp++, n-- )
	    {
		clos		 = (Node *)hp;
		clos->cl.info    = &ground_info;
		clos->cl.args[0] = *argp;
		hp		+= closure_node_size(1);

		susp	     = (Node *)hp;
		susp->s.info = &ground_suspend_info;
		susp->s.fn   = clos;
		susp->s.spc  = ss;
		hp	    += suspend_node_size;

		*argp = susp;
	    }

	    ASSERT((Node *)hp == node);
	    hp  += sz;
	}
    }

    sp += 1;
    RETURN(node);
}
