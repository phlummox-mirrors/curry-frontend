#line 17 "vector.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "trail.h"
#include "eval.h"
#include "threads.h"
#include "trace.h"
#include "cam.h"

enum { VECTOR_TAG };

static NodeInfo vector_info = {
    VECTOR_TAG, 0, (const int *)0, (Label)eval_whnf, "(,)", (FinalFun)0
};
static struct vector_node empty = {
    &vector_info, vector_node_size(0), { }
};

#line 45 "vector.nw"
DECLARE_ENTRYPOINT(__newIOVector);

FUNCTION(__newIOVector)
{
    long i, n;
    Node *init, *vec;

    EXPORT_LABEL(__newIOVector)
 ENTRY_LABEL(__newIOVector)
    EVAL_RIGID_INT(__newIOVector);
    n = int_val(sp[0]);
    if ( n < 0 )
    {
	fprintf(stderr, "newIOVector: bad length (%ld)\n", n);
	exit(2);
    }

    if ( n == 0 )
	vec = (Node *)&empty;
    else
    {
	CHECK_HEAP(vector_node_size(n));
	init = sp[1];
	while ( is_boxed(init) && is_indir_node(init) )
	    init = init->n.node;
	vec	      = (Node *)hp;
	vec->a.info   = &vector_info;
	vec->a.length = vector_node_size(n);
	for ( i = 0; i < n; i++ )
	    vec->a.args[i] = init;
	hp += vector_node_size(n);
    }

    sp += 3;
    RETURN(vec);
}

#line 88 "vector.nw"
DECLARE_ENTRYPOINT(__copyIOVector);

FUNCTION(__copyIOVector)
{
    Node *vec;

    EXPORT_LABEL(__copyIOVector)
 ENTRY_LABEL(__copyIOVector)
    EVAL_RIGID(__copyIOVector);
    ASSERT(node_tag(sp[0]) == VECTOR_TAG);

    vec = sp[0];
    if ( vector_argc(vec) > 0 )
    {
	CHECK_HEAP(vec->a.length);
	vec = (Node *)hp;
	memcpy(vec, sp[0], sp[0]->a.length * word_size);
	hp += vec->a.length;
    }

    sp += 2;
    RETURN(vec);
}

#line 119 "vector.nw"
DECLARE_ENTRYPOINT(__readIOVector);
DECLARE_LABEL(__readIOVector_1);

FUNCTION(__readIOVector)
{
    Node *aux;

    EXPORT_LABEL(__readIOVector)
 ENTRY_LABEL(__readIOVector)
    EVAL_RIGID(__readIOVector);
    ASSERT(node_tag(sp[0]) == VECTOR_TAG);

    aux	  = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(__readIOVector_1);
}

static
FUNCTION(__readIOVector_1)
{
    int  i;
    Node *vec, *r;

 ENTRY_LABEL(__readIOVector_1)
    EVAL_RIGID_INT(__readIOVector_1);

    i	= int_val(sp[0]);
    vec = sp[1];
    sp += 3;
    if ( i < 0 || (unsigned)i >= vector_argc(vec) )
    {
	fprintf(stderr, "readIOVector: index out range (%d)\n", i);
	exit(2);
    }

    r = vec->a.args[i];
    RETURN(r);
}

#line 165 "vector.nw"
DECLARE_ENTRYPOINT(__writeIOVector);
DECLARE_LABEL(__writeIOVector_1);

FUNCTION(__writeIOVector)
{
    Node *aux;

    EXPORT_LABEL(__writeIOVector)
 ENTRY_LABEL(__writeIOVector)
    EVAL_RIGID(__writeIOVector);
    ASSERT(node_tag(sp[0]) == VECTOR_TAG);

    aux	  = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(__writeIOVector_1);
}

static
FUNCTION(__writeIOVector_1)
{
    int  i;
    Node *vec, *node;

 ENTRY_LABEL(__writeIOVector_1)
    EVAL_RIGID_INT(__writeIOVector_1);

    i	 = int_val(sp[0]);
    vec	 = sp[1];
    node = sp[2];
    sp	+= 4;

    if ( i < 0 || (unsigned)i >= vector_argc(vec) )
    {
	fprintf(stderr, "writeIOVector: index out range (%d)\n", i);
	exit(2);
    }

    SAVE(vec, a.args[i]);
    vec->a.args[i] = node;
    RETURN(unit);
}

#line 215 "vector.nw"
DECLARE_ENTRYPOINT(__lengthIOVector);

FUNCTION(__lengthIOVector)
{
    int  n;
    Node *r;

    EXPORT_LABEL(__lengthIOVector)
 ENTRY_LABEL(__lengthIOVector)
    EVAL_RIGID(__lengthIOVector);
    ASSERT(node_tag(sp[0]) == VECTOR_TAG);

    n	= vector_argc(sp[0]);
    sp += 1;

#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = n;
    hp	   += int_node_size;
#else
    r = mk_int(n);
#endif
    RETURN(r);
}
