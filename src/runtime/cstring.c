#line 23 "cstring.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "eval.h"
#include "cstring.h"
#include "cam.h"
#include "trace.h"

#line 45 "cstring.nw"
Node *
from_string(const char *cp)
{
    return prefix_string(cp, nil);
}

Node *
prefix_string(const char *cp, Node *list)
{
    int l = strlen(cp);

    if ( l > 0 )
    {
	Node *tail;
	ADD_LOCAL_ROOTS1(list);
#define list LOCAL_ROOT[0]
	CHECK_HEAP(l * cons_node_size);

	cp  += l;
	tail = list;
	DROP_LOCAL_ROOTS();
#undef list

	do
	{
	    list	    = (Node *)hp;
	    list->c.info    = &cons_info;
	    list->c.args[0] = (Node *)(char_table + (*--cp & 0xff));
	    list->c.args[1] = tail;
	    hp		   += cons_node_size;
	    tail	    = list;
	}
	while ( --l > 0 );
    }
    return list;
}

#line 88 "cstring.nw"
DECLARE_LABEL(nf_string_1);
DECLARE_LABEL(nf_string_2);

FUNCTION(nf_string)
{
    EXPORT_LABEL(nf_string)
 ENTRY_LABEL(nf_string)
    TRACE(("%I enter nf_string%V\n", 1, sp));
    CHECK_STACK1();
    sp	 -= 1;
    sp[0] = sp[1];
    GOTO(nf_string_1);
}

static
FUNCTION(nf_string_1)
{
    Node *list;

 ENTRY_LABEL(nf_string_1)
    EVAL_RIGID(nf_string_1);
    list = sp[0];
    switch ( node_tag(list) )
    {
    case NIL_TAG:
	list = sp[1];
	sp  += 2;
	RETURN(list);
    case CONS_TAG:
	CHECK_STACK1();
	sp   -= 1;
	sp[0] = list->c.args[0];
	sp[1] = list->c.args[1];
	GOTO(nf_string_2);
    default:
	break;
    }
    fprintf(stderr, "nf_string: invalid argument\n");
    exit(2);
}

static
FUNCTION(nf_string_2)
{
 ENTRY_LABEL(nf_string_2)
    EVAL_RIGID_CHAR(nf_string_2);
    sp++;

    /* continue to evaluate the tail of the string */
    GOTO(nf_string_1);
}

#line 150 "cstring.nw"
unsigned
string_length(Node *list)
{
    unsigned n = 0;

    while ( list->info->tag == INDIR_TAG )
	list = list->n.node;
    while ( list->info->tag == CONS_TAG )
    {
	n++;
	list = list->c.args[1];
	while ( list->info->tag == INDIR_TAG )
	    list = list->n.node;
    }
    ASSERT(list->info->tag == NIL_TAG);
    return n;
}

char *
copy_string(Node *list, char *buf)
{
    char *cp = buf;
    Node *head;

    while ( list->info->tag != NIL_TAG )
	switch ( list->info->tag )
	{
	case INDIR_TAG:
	    list = list->n.node;
	    break;
	case CONS_TAG:
	    head = list->c.args[0];
	    while ( is_boxed(head) && head->info->tag == INDIR_TAG )
		head = head->n.node;
	    ASSERT(is_boxed(head) && is_char_node(head));
	    *cp++ = head->ch.ch;
	    list  = list->c.args[1];
	    break;
	default:
	    fprintf(stderr,
		    "copy_string: Invalid string or not in normal form\n");
	    exit(1);
	}
    *cp = '\0';
    return buf;
}

char *
to_string(Node *list)
{
    unsigned n   = string_length(list);
    char     *cp = (char *)malloc(n + 1);

    if ( cp == (char *)0 )
    {
	fprintf(stderr, "to_string: memory exhausted\n");
	exit(1);
    }

    return copy_string(list, cp);
}
