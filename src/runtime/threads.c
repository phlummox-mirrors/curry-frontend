#line 30 "threads.nw"
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
#include "spaces.h"
#include "search.h"
#include "trail.h"
#include "trace.h"

unsigned int	    cid;
static unsigned int tid;
Node		    **ds_base;

#line 114 "threads.nw"
#define thread_node_size	wordsof(union thread_node)
#define thread_state_size	wordsof(struct thread_state)
#define thread_surrogate_size	wordsof(struct thread_surrogate)

static const int ot_thread[] = {
    2,
    word_offsetof(struct thread_state, next),
    word_offsetof(struct thread_state, ds)
};
static NodeInfo thread_info = {
    THREAD_TAG, thread_state_size, ot_thread, (Label)no_eval, (const char *)0,
    (FinalFun)0
};

static const int ot_surrogate[] = {
    3,
    word_offsetof(struct thread_surrogate, next),
    word_offsetof(struct thread_surrogate, thd),
    word_offsetof(struct thread_surrogate, link)
};
static NodeInfo surrogate_info = {
    THREAD_TAG, thread_surrogate_size, ot_surrogate, (Label)no_eval,
    (const char *)0, (FinalFun)0
};

ThreadQueue rq;

#line 158 "threads.nw"
static const char   *reasons[] = { "None", "Yield", "Delay", "Eval" };

#line 216 "threads.nw"
static void new_thread(void);
static Label activate_thread(void);
static void terminate_thread(void);
static ThreadQueue interrupt_thread(Label, enum suspend_reason);
static ExceptionFrame *relocate_thread(ExceptionFrame *, int);

static NodeInfo saved_stack_info = {
    0, 0, (const int *)0, (Label)no_eval, (const char *)0, (FinalFun)0
};

#line 240 "threads.nw"
void
start_thread(unsigned int n)
{
    ThreadQueue thd;
    Label	contIp;

    ASSERT(n > 0);

    /* start a new thread */
    contIp = (Label)sp[n-1];
    if ( contIp != (Label)0 )
    {
	thd	    = interrupt_thread(contIp, None);
	thd->t.next = rq;
	rq	    = thd;
    }
    new_thread();
    TRACE(("%I starting\n"));

    /* move the initial stack to the new thread */
    ds_base += n;
    if ( rq != (ThreadQueue)0 )
	rq->t.ds_size -= n;

    /* save the ultimate return address */
    sp[n-1] = (Node *)stop_thread;
}

#line 273 "threads.nw"
FUNCTION(stop_thread)
{
    EXPORT_LABEL(stop_thread)
 ENTRY_LABEL(stop_thread)

    TRACE(("%I terminated\n"));
    terminate_thread();
    GOTO(activate_thread());
}

#line 291 "threads.nw"
Label
suspend_thread(Label l, Node *susp)
{
    ThreadQueue thd;

    ASSERT(is_boxed(susp) && (is_suspend_node(susp) || is_queueMe_node(susp)));
    if ( !is_local_space(susp->q.spc) )
	return suspend_search(l, susp, Eval);

    {
	ADD_LOCAL_ROOTS1(susp);
#define susp LOCAL_ROOT[0]
	thd = interrupt_thread(l, Eval);
	SAVE(susp, q.wq);
	thd->t.next = susp->q.wq;
	susp->q.wq  = thd;
#undef susp
    	DROP_LOCAL_ROOTS();
    }
    return activate_thread();
}

Label
delay_thread(Label l, Node *var)
{
    ThreadQueue thd;

    ASSERT(is_boxed(var) && is_variable_node(var));
    if ( !is_local_space(var->v.spc) )
	return suspend_search(l, var, Delay);

    {
	ADD_LOCAL_ROOTS1(var);
#define var LOCAL_ROOT[0]
	thd = interrupt_thread(l, Delay);
	SAVE(var, v.wq);
	thd->t.next = var->v.wq;
	var->v.wq   = thd;
#undef var
	DROP_LOCAL_ROOTS();
    }
    return activate_thread();
}

#line 343 "threads.nw"
Label
yield_thread(Label l)
{
    ThreadQueue thd;

    if ( rq == (ThreadQueue)0 )
	return l;

    thd	= interrupt_thread(l, Yield);
    rq	= join_queues(rq, thd);
    return activate_thread();
}

Label
yield_delay_thread(Label l, Node *var)
{
    ThreadQueue thd;

    ASSERT(is_boxed(var) && is_variable_node(var));
    if ( !is_local_space(var->v.spc) )
	return suspend_search(l, var, Delay);

    if ( rq == (ThreadQueue)0 )
	return l;

    {
	ADD_LOCAL_ROOTS2(var, (Node *)0);
#define var LOCAL_ROOT[0]
#define thd1 (ThreadQueue)LOCAL_ROOT[1]

	ASSERT(is_boxed(var) && is_variable_node(var));
	thd1 = interrupt_thread(l, Yield);

	CHECK_HEAP(2*thread_surrogate_size);
	SAVE(var, v.wq);
	thd	    = (ThreadQueue)hp;
	thd->s.info = &surrogate_info;
	thd->s.id   = 0;
	thd->s.thd  = thd1;
	thd->s.next = var->v.wq;
	thd->s.link = (ThreadQueue)(hp + thread_surrogate_size);
	var->v.wq   = thd;

	thd	    = (ThreadQueue)(hp + thread_surrogate_size);
	thd->s.info = &surrogate_info;
	thd->s.id   = 0;
	thd->s.thd  = thd1;
	thd->s.next = (ThreadQueue)0;
	thd->s.link = (ThreadQueue)hp;
	hp	   += 2*thread_surrogate_size;
#undef thd1
#undef var
	DROP_LOCAL_ROOTS();
    }

    rq  = join_queues(rq, thd);
    return activate_thread();
}

#line 411 "threads.nw"
Label
activate_threads(ThreadQueue wq, Label l)
{
    ThreadQueue thd;

    while ( wq != (ThreadQueue)0 && wq->t.id == 0
	    && wq->s.thd == (ThreadQueue)0 )
	wq = wq->t.next;
    if ( wq == (ThreadQueue)0 )
	return l;

    {
	ADD_LOCAL_ROOTS1((Node *)wq);
#define wq (ThreadQueue)LOCAL_ROOT[0]
	thd		= interrupt_thread(l, None);
	thd->t.next = rq;
	rq		= join_queues(wq, thd);
#undef wq
	DROP_LOCAL_ROOTS();
    }
    return activate_thread();
}

void
wake_threads(ThreadQueue wq)
{
    while ( wq != (ThreadQueue)0 && wq->t.id == 0
	    && wq->s.thd == (ThreadQueue)0 )
	wq = wq->t.next;
    rq = join_queues(wq, rq);
}

#line 449 "threads.nw"
ThreadQueue
join_queues(ThreadQueue tq1, ThreadQueue tq2)
{
    ThreadQueue tq;

    /* return the other queue if one queue is empty */
    if ( tq1 == (ThreadQueue)0 )
	tq = tq2;
    else if ( tq2 == (ThreadQueue)0 )
	tq = tq1;

    /* otherwise append tq2 to tq1 (destructively) */
    else
    {
	tq = tq1;
	while ( tq1->t.next != (ThreadQueue)0 )
	    tq1 = tq1->t.next;
	SAVE(tq1, t.next);
	tq1->t.next = tq2;
    }

    return tq;
}

#line 478 "threads.nw"
static void
new_thread()
{
    /* initialize the thread state */
    if ( tid == 0 )
	tid++;
    cid	    = tid++;
    ds_base = sp;
    efp	    = (ExceptionFrame *)0;
}

#line 495 "threads.nw"
static Label
activate_thread()
{
    Label		ip;
    ThreadQueue		thd, sur;
    enum suspend_reason reason;

    /* check for a deadlock */
    if ( rq == (ThreadQueue)0 )
	return nondet_handlers.deadlock;

    /* activate the head of the ready queue */
    thd = rq;
    rq  = thd->t.next;
    while ( rq != (ThreadQueue)0 && rq->t.id == 0
	    && rq->s.thd == (ThreadQueue)0 )
	rq = rq->t.next;
    if ( thd->t.id == 0 )
    {
	sur = thd;
	thd = (ThreadQueue)sur->s.thd;
	ASSERT(thd->t.id != 0);
	while ( sur->s.thd != (ThreadQueue)0 )
	{
	    ASSERT(sur->s.id == 0 && sur->s.link != (ThreadQueue)0);
	    SAVE(sur, s.thd);
	    sur->s.thd = (ThreadQueue)0;
	    sur	       = sur->s.link;
	}
    }
    cid	   = thd->t.id;
    ip	   = thd->t.ip;
    reason = (enum suspend_reason)thd->t.reason;

    /* eventually restore the stack */
    if ( thd->t.ds != (Node *)0 )
    {
	CHECK_STACK(thd->t.ds_size);
	ASSERT(thd->t.ds_size == vector_argc(thd->t.ds));
	ds_base = sp;
	sp     -= thd->t.ds_size;
	memcpy(sp, thd->t.ds->a.args, thd->t.ds_size * word_size);
    }
    else
	ds_base	= sp + thd->t.ds_size;

    /* eventually relocate the exception handler chain */
    efp = thd->t.efp;
    if ( efp != (ExceptionFrame *)0 && ds_base != thd->t.ds_base )
	efp = relocate_thread(efp, ds_base - thd->t.ds_base);

    /* return the continuation address of the thread */
    if ( reason != None )
	TRACE(("%I resume (%s)\n", reasons[reason]));
    return ip;
}

#line 557 "threads.nw"
static void
terminate_thread()
{
    /* deallocate the current thread */
    sp	= ds_base;
}

#line 570 "threads.nw"
static ThreadQueue
interrupt_thread(Label l, enum suspend_reason reason)
{
    Node	 *ds;
    ThreadQueue  thd;
    boolean	 save_ds = reason != None;
    unsigned int ds_size = ds_base - sp;

    CHECK_HEAP(thread_state_size + (save_ds ? vector_node_size(ds_size) : 0));

    if ( reason != None )
	TRACE(("%I suspend (%s)\n", reasons[reason]));

    /* eventually save the stack */
    if ( save_ds )
    {
	ds	     = (Node *)hp;
	ds->a.info   = &saved_stack_info;
	ds->a.length = vector_node_size(ds_size);
	memcpy(ds->a.args, sp, ds_size * word_size);
	hp	    += vector_node_size(ds_size);
	sp	     = ds_base;
    }
    else
	ds = (Node *)0;

    /* save the thread state */
    ASSERT(cid != 0);
    thd		   = (ThreadQueue)hp;
    thd->t.info	   = &thread_info;
    thd->t.id	   = cid;
    thd->t.next	   = (ThreadQueue)0;
    thd->t.reason  = reason;
    thd->t.ip	   = l;
    thd->t.efp	   = efp;
    thd->t.ds_base = ds_base;
    thd->t.ds_size = ds_size;
    thd->t.ds	   = ds;
    hp		  += thread_state_size;

    /* return the thread */
    return thd;
}

#line 619 "threads.nw"
static ExceptionFrame *
relocate_thread(ExceptionFrame *efp, int dist)
{
    ExceptionFrame *fp;

    if ( efp != (ExceptionFrame *)0 )
    {
	efp = (ExceptionFrame *)((Node **)efp + dist);
	for ( fp = efp; fp->frame != (ExceptionFrame *)0; fp = fp->frame )
	    fp->frame = (ExceptionFrame *)((Node **)fp->frame + dist);
    }

    return efp;
}

#line 645 "threads.nw"
Node *
save_continuation(Label l, Node **ds_base)
{
    unsigned int ds_size = ds_base - sp;
    Node	 *cont, *savedDs;
    ThreadQueue  thd;

    ASSERT(ds_size >= 0);

    /* interrupt the current thread */
    thd		= interrupt_thread((Label)0, None);
    thd->t.next = rq;
    rq		= thd;

    /* save the current machine state */
    CHECK_HEAP(search_cont_node_size + vector_node_size(ds_size));

    savedDs	      = (Node *)hp;
    savedDs->a.info   = &saved_stack_info;
    savedDs->a.length = vector_node_size(ds_size);
    memcpy(savedDs->a.args, sp, ds_size * word_size);
    hp		     += vector_node_size(ds_size);

    /* save the state into a new search continuation */
    cont	  = (Node *)hp;
    cont->sc.info = &search_cont_info;
    cont->sc.code = l;
    cont->sc.susp = (Node *)0;
    cont->sc.var  = (Node *)0;
    cont->sc.ds   = savedDs;
    cont->sc.rq   = rq;
    cont->sc.spc  = ss;
    hp		 += search_cont_node_size;

    /* return the search continuation */
    return cont;
}

void
restore_continuation(Node *cont)
{
    unsigned int ds_size;
    ThreadQueue	 tq;

    ASSERT(is_search_cont_node(cont));

    /* check for enough space on the stack */
    ds_size = vector_argc(cont->sc.ds);
    CHECK_STACK(ds_size);

    /* move the data stack of the current thread */
    memcpy(sp - ds_size, sp, (ds_base - sp)*word_size);
    sp	    -= ds_size;
    ds_base -= ds_size;
    if ( efp != (ExceptionFrame *)0 )
	efp = relocate_thread(efp, -ds_size);

    /* restore the continuation's data stack below the current stack */
    memcpy(ds_base, cont->sc.ds->a.args, ds_size*word_size);

    /* update the continuation address of the first restored thread */
    tq = cont->sc.rq;
    ASSERT(tq != (ThreadQueue)0 && tq->t.id != 0);
    tq->t.ip = cont->sc.code;

    /* wake all threads of the search space and add them to the ready queue */
    wake_threads(tq);
}

Label
resume_continuation(Node *cont)
{
    unsigned int ds_size;

    ASSERT(is_search_cont_node(cont));

    /* check for enough space on the stacks */
    ds_size = vector_argc(cont->sc.ds);
    CHECK_STACK(ds_size);

    /* restore the continuation's ready queue */
    ASSERT(cont->sc.rq != (ThreadQueue)0 && cont->sc.rq->t.id != 0);
    rq = cont->sc.rq;

    /* restore the continuation's data stack */
    sp -= ds_size;
    memcpy(sp, cont->sc.ds->a.args, ds_size*word_size);

    /* update the continuation address of the first restored thread */
    rq->t.ip = cont->sc.code;

    /* activate the first thread */
    return activate_thread();
}
