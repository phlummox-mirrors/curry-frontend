#line 14 "constraints.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "eval.h"
#include "threads.h"
#include "spaces.h"
#include "cam.h"
#include "trace.h"

DECLARE_ENTRYPOINT(__success);

FUNCTION(__success)
{
    EXPORT_LABEL(__success)
 ENTRY_LABEL(__success)
    RETURN(Success);
}

#line 53 "constraints.nw"
DECLARE_ENTRYPOINT(___38_);
DECLARE_LABEL(___38__1);
DECLARE_LABEL(___38__2);

FUNCTION(___38_)
{
    Node *c1, *c2, *aux;

    EXPORT_LABEL(___38_)
 ENTRY_LABEL(___38_)

    for ( c1 = sp[0]; node_tag(c1) == INDIR_TAG; c1 = c1->n.node )
	;
    for ( c2 = sp[1]; node_tag(c2) == INDIR_TAG; c2 = c2->n.node )
	;

    switch ( node_tag(c1) )
    {
    case CLOSURE_TAG:
	switch ( node_tag(c2) )
	{
	case CLOSURE_TAG:
	    sp[0] = c1;
	    sp[1] = c2;
	    CHECK_HEAP(queueMe_node_size);
	    aux	       = (Node *)hp;
	    aux->info  = &queueMe_info;
	    aux->q.wq  = (ThreadQueue)0;
	    aux->q.spc = ss;
	    hp	      += queueMe_node_size;
	    CHECK_STACK(4);
	    sp	 -= 4;
	    sp[0] = sp[4];
	    sp[1] = (Node *)update;
	    sp[2] = aux;
	    sp[3] = (Node *)___38_;
	    sp[4] = aux;
	    start_thread(4);
	    GOTO(sp[0]->info->eval);
	case SUSPEND_TAG:
	    aux = c1;
	    c1	= c2;
	    c2	= aux;
	    break;
	}
	/* FALL THROUGH!!! */
    case SUSPEND_TAG:
	switch ( node_tag(c2) )
	{
	case CLOSURE_TAG:
	case SUSPEND_TAG:
	    CHECK_STACK(2);
	    sp	 -= 2;
	    sp[0] = c1;
	    sp[1] = (Node *)___38_;
	    sp[2] = c1;
	    sp[3] = c2;
	    start_thread(2);
	    GOTO(sp[0]->info->eval);
	case QUEUEME_TAG:
	case VARIABLE_TAG:
	    CHECK_STACK1();
	    sp	 -= 1;
	    sp[0] = c1;
	    sp[1] = (Node *)___38__1;
	    sp[2] = c2;
	    GOTO(c1->info->eval);
	case SUCCESS_TAG:
	    *++sp = c1;
	    GOTO(c1->info->eval);
	}
	break;
    case QUEUEME_TAG:
	switch ( node_tag(c2) )
	{
	case CLOSURE_TAG:
	case SUSPEND_TAG:
	    CHECK_STACK1();
	    sp	 -= 1;
	    sp[0] = c2;
	    sp[1] = (Node *)___38__1;
	    sp[2] = c1;
	    GOTO(c2->info->eval);
	case QUEUEME_TAG:
	case VARIABLE_TAG:
	    CHECK_STACK1();
	    sp	 -= 1;
	    sp[0] = c1;
	    sp[1] = (Node *)___38__1;
	    sp[2] = c2;
	    GOTO(c1->info->eval);
	case SUCCESS_TAG:
	    *++sp = c1;
	    GOTO(c1->info->eval);
	}
	break;
    case VARIABLE_TAG:
	/* evaluate the other argument then delay */
	switch ( node_tag(c2) )
	{
	case CLOSURE_TAG:
	case SUSPEND_TAG:
	case QUEUEME_TAG:
	    CHECK_STACK1();
	    sp	 -= 1;
	    sp[0] = c2;
	    sp[1] = (Node *)___38__1;
	    sp[2] = c1;
	    GOTO(c2->info->eval);
	case VARIABLE_TAG:
	    sp[0] = c1;
	    sp[1] = c2;
	    GOTO(delay_thread(___38__2, c1));
	case SUCCESS_TAG:
	    sp += 2;
	    RETURN(c1);
	}
	break;
    case SUCCESS_TAG:
	/* trivial case */
	switch ( node_tag(c2) )
	{
	case CLOSURE_TAG:
	case SUSPEND_TAG:
	case QUEUEME_TAG:
	    *++sp = c2;
	    GOTO(c2->info->eval);
	case VARIABLE_TAG:
	case SUCCESS_TAG:
	    sp += 2;
	    RETURN(c2);
	}
	break;
    }
    fprintf(stderr, "(&) invalid argument\n");
    exit(2);
}

#line 200 "constraints.nw"
static
FUNCTION(___38__1)
{
    Node *c1, *c2;

 ENTRY_LABEL(___38__1)
    /* if the evaluated argument is now success return the other one */
    for ( c1 = sp[0]; node_tag(c1) == INDIR_TAG; c1 = c1->n.node )
	;
    c2 = sp[1];
    if ( node_tag(c1) == SUCCESS_TAG )
    {
    again_1:
        switch ( node_tag(c2) )
        {
	case INDIR_TAG:
	    c2 = c2->n.node;
	    goto again_1;
	case QUEUEME_TAG:
	    *++sp = c2;
	    GOTO(c2->info->eval);
	case VARIABLE_TAG:
	case SUCCESS_TAG:
	    sp += 2;
	    RETURN(c2);
	default:
	    fprintf(stderr, "(&): invalid argument\n");
	    exit(2);
	}
    }

    /* wait for the other argument being evaluated if it is a queue-me */
    ASSERT(node_tag(c1) == VARIABLE_TAG);
 again_2:
    switch ( node_tag(c2) )
    {
    case INDIR_TAG:
	c2 = c2->n.node;
	goto again_2;
    case QUEUEME_TAG:
	CHECK_STACK1();
	sp   -= 1;
	sp[0] = c2;
	sp[1] = (Node *)___38__1;
	sp[2] = c1;
	GOTO(c2->info->eval);
    case VARIABLE_TAG:
	sp[0] = c1;
	sp[1] = c2;
	GOTO(delay_thread(___38__2, c1));
    case SUCCESS_TAG:
        break;
    }

    sp += 2;
    RETURN(c1);
}

#line 266 "constraints.nw"
static
FUNCTION(___38__2)
{
    Node *c1, *c2;

 ENTRY_LABEL(___38__2)
    for ( c1 = sp[0]; node_tag(c1) == INDIR_TAG; c1 = c1->n.node )
	;
    for ( c2 = sp[1]; node_tag(c2) == INDIR_TAG; c2 = c2->n.node )
	;
    ASSERT(node_tag(c1) == SUCCESS_TAG);
    ASSERT(node_tag(c2) == SUCCESS_TAG || node_tag(c2) == VARIABLE_TAG);

    sp += 2;
    RETURN(c2);
}
