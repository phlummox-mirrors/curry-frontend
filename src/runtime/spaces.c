#line 35 "spaces.nw"
#include "config.h"
#include "debug.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "spaces.h"
#include "trail.h"
#include "eval.h"
#include "vars.h"

static void switch_bindings(SearchSpace *space);
static void finalize_search_space(Node *);
static Node *copy_node(Node *node, SearchSpace *space);

static NodeInfo search_space_info = {
    0, wordsof(struct search_space), (const int *)0, (Label)no_eval, (const char *)0,
    finalize_search_space
};

struct search_space *ss;

#line 98 "spaces.nw"
static const int ot_script[] = {
    -wordsof(ScriptRec), 3,
    word_offsetof(ScriptRec, addr),
    word_offsetof(ScriptRec, inVal),
    word_offsetof(ScriptRec, outVal)
};
static NodeInfo script_info = {
    SCRIPT_TAG, 0, ot_script, (Label)no_eval, (const char *)0, (FinalFun)0
};

#line 128 "spaces.nw"
static void
switch_bindings(SearchSpace *space)
{
    unsigned int n;
    ScriptRec	 *script;
    SearchSpace	 *root, *common, *child, *parent;

    root = space->root;

    /* Return if the space is already active */
    if ( root->active == space )
	return;

    /* Phase 1: mark everything upto the root and reverse parent pointers */
    child = (SearchSpace *)0;
    while ( space != (SearchSpace *)0 )
    {
	parent	      = space->parent;
	space->parent = (SearchSpace *)((long)child | 0x01);
	child 	      = space;
	space 	      = parent; 
    }

    /* Phase 2: undo bindings up to closest common ancestor */
    space = root->active;
    while ( !((long)space->parent & 0x01) )
    {
	if ( space->script != (Script *)0 )
	{
	    n	   = vector_argc(space->script) / wordsof(ScriptRec);
	    script = space->script->data + n;
	    while ( n-- > 0 )
	    {
		--script;
		ASSERT(heap_base <= script->addr && script->addr < heap_end);
		script->addr[INFO_OFS]	  = script->outInfo;
		script->addr[script->ofs] = script->outVal;
	    }
	}
	space = space->parent;
    }

    /* Phase 3: unmark everything and activate bindings of new space */
    common = space;
    parent = (SearchSpace *)0;
    space  = root;
    while ( space != (SearchSpace *)0 )
    {
	child	      = (SearchSpace *)((long)space->parent & ~0x01);
	space->parent = parent;
	if ( space == common )
	    common = (SearchSpace *)0;
	else if ( common == (SearchSpace *)0 )
	    if ( space->script != (Script *)0 )
	    {
		n = vector_argc(space->script) / wordsof(ScriptRec);
		script = space->script->data;
		for ( ; n-- > 0; script++ )
		{
		    ASSERT(heap_base <= script->addr
			   && script->addr < heap_end);
		    script->addr[INFO_OFS]    = script->inInfo;
		    script->addr[script->ofs] = script->inVal;
		}
	    }
	parent	      = space;
	space	      = child;
    }

    /* The new space is now active */
    root->active = parent;
}

#line 218 "spaces.nw"
static void
finalize_search_space(Node *node)
{
    unsigned	n;
    ScriptRec	*script;
    SearchSpace *space = (SearchSpace *)node;

    /* do nothing during "normal" gc or when root is dead */
    if ( !in_gc && (word *)space->root < hlim && space->root->active == space )
    {
	for ( ; (word *)space >= hlim; space = space->parent )
	    if ( space->script != (Script *)0 )
	    {
		n = vector_argc(space->script) / wordsof(ScriptRec);
		script = space->script->data + n;
		while ( n-- > 0 )
		{
		    --script;
		    ASSERT(heap_base <= script->addr
			   && script->addr < heap_end);
		    script->addr[INFO_OFS]    = script->outInfo;
		    script->addr[script->ofs] = script->outVal;
		}
	    }
	space->root->active = space;
    }
}

#line 256 "spaces.nw"
void
new_search_space(SearchSpace *parentSpace)
{
    SearchSpace *newSpace;
    ADD_LOCAL_ROOTS1((Node *)parentSpace);
#define parentSpace ((SearchSpace *)LOCAL_ROOT[0])

    /* activate the parent's bindings */
    if ( parentSpace != (SearchSpace *)0 )
	switch_bindings(parentSpace);

    /* allocate the new search space */
    CHECK_HEAP(wordsof(SearchSpace));
    ss = newSpace    = (SearchSpace *)hp;
    newSpace->info   = &search_space_info;
    newSpace->root   =
	parentSpace == (SearchSpace *)0 ? newSpace : parentSpace->root;
    newSpace->parent = parentSpace;
    newSpace->active = (SearchSpace *)0;
    newSpace->script = (Script *)0;
    hp		    += wordsof(SearchSpace);
    register_final((Node *)newSpace);

#undef parentSpace
    DROP_LOCAL_ROOTS();
}

#line 294 "spaces.nw"
boolean
inject_search_space(SearchSpace *space)
{
    /* fail if current space is not a root space */
    if ( ss == (SearchSpace *)0 || ss->parent != (SearchSpace *)0 )
	return false;

    /* otherwise re-parent the current space */
    ss->root   = space->root;
    ss->parent = space;

    /* activate the parent's bindings and succeed */
    switch_bindings(space);
    return true;
}

#line 318 "spaces.nw"
void
save_search_space()
{
    unsigned int n;
    SaveRec	 *trail;
    ScriptRec	 *script;

    ASSERT(ss != (SearchSpace *)0);

    /* save the current trail segment into the search space */
    n = tp - bp->btTp;
    if ( n > 0 )
    {
	CHECK_HEAP(vector_node_size(n * wordsof(ScriptRec)));

	/* initialize the script */
	ss->script	   = (Script *)hp;
	ss->script->info   = &script_info;
	ss->script->length = vector_node_size(n * wordsof(ScriptRec));
	hp		  += vector_node_size(n * wordsof(ScriptRec));

	script = ss->script->data + n;
	trail  = tp;
	while ( n-- > 0 )
	{
	    trail--;
	    script--;
	    script->addr    = trail->addr;
	    script->inInfo  = trail->addr[INFO_OFS];
	    script->outInfo = trail->info;
	    script->ofs     = trail->ofs;
	    script->inVal   = trail->addr[trail->ofs];
	    script->outVal  = trail->val;
	}
    }

    /* this search space is now active */
    ss->root->active = ss;
}

#line 367 "spaces.nw"
void
discard_search_space()
{
    /* undo the bindings of the current space */
    RESTORE(bp->btTp);

    /* release the memory allocated in the current space */
    release_names(bp->btDict);
    release_mem();
}

#line 386 "spaces.nw"
void
resume_search_space(SearchSpace *space)
{
    unsigned int i, n;
    ScriptRec	 *script;

    ASSERT(space != (SearchSpace *)0);

    /* change the current search space and activate its bindings */
    ss = space;
    switch_bindings(ss);

    /* restore the trail */
    if ( ss->script != (Script *)0 )
    {
	n = vector_argc(ss->script) / wordsof(ScriptRec);
	CHECK_TRAIL(n);

	script     = ss->script->data;
	ss->script = (Script *)0;
	for ( i = 0; i < n; i++ )
	{
	    tp->addr = script->addr;
	    tp->info = script->outInfo;
	    tp->ofs  = script->ofs;
	    tp->val  = script->outVal;
	    tp++;
	    script++;
	}
    }
}

#line 459 "spaces.nw"
static Node **alloc;			/* temp. allocation pointer */
static Node **ntp;			/* used for saving updated node */

#line 467 "spaces.nw"
#define FORWARD_FLAG		0x01
#define is_forwarded(node)	((int)(node)->info & FORWARD_FLAG)
#define forward(node,new)	((node)->info = (NodeInfo *)((int)(new) | FORWARD_FLAG))
#define get_forward(node)       ((Node *)((int)(node)->info & ~FORWARD_FLAG))

#line 477 "spaces.nw"
static jmp_buf restart_copy;

#line 487 "spaces.nw"
static Node *
copy_node(Node *node, SearchSpace *space)
{
    boolean	 do_copy;
    unsigned int sz;

    while ( is_boxed(node) && node >= (Node *)heap_base && node < (Node *)hp )
    {
	/* check for a node that is already forwarded */
	if ( is_forwarded(node) )
	    node = get_forward(node);

	/* check whether we can/must share the node */
	else
	{
	    switch ( node_tag(node) )
	    {
	    case CHAR_TAG:
	    case INT_TAG:
	    case FLOAT_TAG:
		do_copy = false;
		break;

	    case INDIR_TAG:
		node = node->n.node;
		continue;

	    case VARIABLE_TAG:
		do_copy = node->v.spc != (SearchSpace *)0
		    && node->v.spc->root == space->root;
		break;
	    case SUSPEND_TAG:
		do_copy = node->s.spc != (SearchSpace *)0
		    && node->s.spc->root == space->root;
		break;
	    case QUEUEME_TAG:
		do_copy = node->q.spc != (SearchSpace *)0
		    && node->q.spc->root == space->root;
		break;

	    case SEARCH_CONT_TAG:
		do_copy = node->sc.spc == space;
		break;

	    default:
		do_copy = !is_abstract_node(node);
		break;
	    }

	    if ( do_copy )
	    {
		/* the node has to be copied check if space is available */
		sz = node_size(node);
		if ( sz == 0 )
		    sz = node->a.length;
		if ( alloc + sz + 1 >= ntp )
		    longjmp(restart_copy, sz + 1);

		/* copy the node to the new location and leave a forwarding
		 * pointer in the original node */
		memcpy(alloc, node, sz * word_size);
		*--ntp = node;
		forward(node, alloc);
		node   = (Node *)alloc;
		alloc += sz;
	    }
	}
	break;
    }

    /* return the new address */
    return node;
}

#line 569 "spaces.nw"
Node *
copy_graph(Node *graph, SearchSpace *space)
{
    boolean	 gc_done = false;
    unsigned int sz;
    Node	 *copy, *scan;
    ADD_LOCAL_ROOTS2(graph, (Node *)space);
#define graph LOCAL_ROOT[0]
#define space (SearchSpace *)LOCAL_ROOT[1]

    /* activate the bindings of the graph's space */
    switch_bindings(space);

    /* handle gc request */
    sz = setjmp(restart_copy);
    if ( sz != 0 )
    {
	if ( gc_done )
	    heap_exhausted();

	sz += alloc - (Node **)hp;
	sz += (Node **)heap_end - ntp;
	for ( ; ntp < (Node **)heap_end; ntp++ )
	{
	    ASSERT(is_forwarded(*ntp));
	    (*ntp)->info = get_forward(*ntp)->info;
	}
	collect(sz);
	gc_done = true;
    }

    /* copy the root of the graph */
    alloc = (Node **)hp;
    ntp	  = (Node **)heap_end;
    copy  = copy_node(graph, space);

    /* copy all children */
    for ( scan = (Node *)hp; scan < (Node *)alloc; (Node **)scan += sz )
    {
	unsigned int i, n;
	ThreadQueue  tq;

	sz = node_size(scan);
	if ( sz == 0 )
	    sz = scan->a.length;

	switch ( node_tag(scan) )
	{
	case CHAR_TAG:
	case INT_TAG:
	case FLOAT_TAG:
	    break;

	case SUSPEND_TAG:
	    scan->s.fn	= copy_node(scan->s.fn, space);
	    scan->s.spc = ss;
	    break;

	case QUEUEME_TAG:
	    scan->q.wq	= (ThreadQueue)copy_node((Node *)scan->q.wq, space);
	    scan->q.spc = ss;
	    break;

	case VARIABLE_TAG:
	    scan->v.cstrs = (Constraint *)copy_node((Node *)scan->v.cstrs, space);
	    scan->v.wq	  = (ThreadQueue)copy_node((Node *)scan->v.wq, space);
	    scan->v.spc	  = ss;
	    break;

	case SEARCH_CONT_TAG:
	    scan->sc.susp = copy_node(scan->sc.susp, space);
	    scan->sc.var  = copy_node(scan->sc.var, space);
	    scan->sc.ds	  = copy_node(scan->sc.ds, space);
	    scan->sc.rq	  = (ThreadQueue)copy_node((Node *)scan->sc.rq, space);
	    scan->sc.spc  = ss;
	    break;

	case THREAD_TAG:
	    tq = (ThreadQueue)scan;
	    if ( tq->t.id != 0 )
	    {
		tq->t.next = (ThreadQueue)copy_node((Node *)tq->t.next, space);
		tq->t.ds   = copy_node(tq->t.ds, space);
	    }
	    else
	    {
		tq->s.next = (ThreadQueue)copy_node((Node *)tq->s.next, space);
		tq->s.thd  = (ThreadQueue)copy_node((Node *)tq->s.thd, space);
		tq->s.link = (ThreadQueue)copy_node((Node *)tq->s.link, space);
	    }
	    break;

	default:
	    if ( is_abstract_node(scan) )
		break;
	    ASSERT(is_constr_node(scan));
	    /* FALL THROUGH*/
	case PAPP_TAG:
	case CLOSURE_TAG:
	    if ( is_vector(scan) )
	    {
		i = 1;
		n = vector_argc(scan) + 1;
	    }
	    else
	    {
		i = 0;
		n = constr_argc(scan);
	    }
	    for ( ; i < n; i++ )
		scan->c.args[i] = copy_node(scan->c.args[i], space);
	    break;
	}
    }
    ASSERT(scan == (Node *)alloc);
    DROP_LOCAL_ROOTS();
#undef graph
#undef space
    hp = (word *)alloc;

    /* restore the old graph and return its copy */
    for ( ; ntp < (Node **)heap_end; ntp++ )
    {
	ASSERT(is_forwarded(*ntp));
	(*ntp)->info = get_forward(*ntp)->info;
    }
    return copy;
}
