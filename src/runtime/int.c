#line 13 "int.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "eval.h"
#include "threads.h"
#include "cam.h"
#include "trace.h"

#line 32 "int.nw"
DECLARE_ENTRYPOINT(___43_);
DECLARE_LABEL(___43__1);

FUNCTION(___43_)
{
    Node *aux;

    EXPORT_LABEL(___43_)
 ENTRY_LABEL(___43_)
    EVAL_RIGID_INT(___43_);
    aux   = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(___43__1);
}

static
FUNCTION(___43__1)
{
#if ONLY_BOXED_OBJECTS
    int  i;
#endif
    Node *r;

 ENTRY_LABEL(___43__1)
    EVAL_RIGID_INT(___43__1);
#if ONLY_BOXED_OBJECTS
    i	= int_val(sp[1]) + int_val(sp[0]);
    sp += 2;

    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = i;
    hp	   += int_node_size;
#else
    r	= (Node *)((long)sp[1] + (long)sp[0] - 1);
    sp += 2;
#endif
    RETURN(r);
}


DECLARE_ENTRYPOINT(___45_);
DECLARE_LABEL(___45__1);

FUNCTION(___45_)
{
    Node *aux;

    EXPORT_LABEL(___45_)
 ENTRY_LABEL(___45_)
    EVAL_RIGID_INT(___45_);
    aux   = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(___45__1);
}

static
FUNCTION(___45__1)
{
#if ONLY_BOXED_OBJECTS
    int	 i;
#endif
    Node *r;

 ENTRY_LABEL(___45__1)
    EVAL_RIGID_INT(___45__1);
#if ONLY_BOXED_OBJECTS
    i	= int_val(sp[1]) - int_val(sp[0]);
    sp += 2;

    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = i;
    hp	   += int_node_size;
#else
    r = (Node *)((long)sp[1] - (long)sp[0] + 1);
    sp += 2;
#endif
    RETURN(r);
}


DECLARE_ENTRYPOINT(___42_);
DECLARE_LABEL(___42__1);

FUNCTION(___42_)
{
    Node *aux;

    EXPORT_LABEL(___42_)
 ENTRY_LABEL(___42_)
    EVAL_RIGID_INT(___42_);
    aux   = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(___42__1);
}

static
FUNCTION(___42__1)
{
#if ONLY_BOXED_OBJECTS
    int	 i;
#endif
    Node *r;

 ENTRY_LABEL(___42__1)
    EVAL_RIGID_INT(___42__1);
#if ONLY_BOXED_OBJECTS
    i	= int_val(sp[1]) * int_val(sp[0]);
    sp += 2;

    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = i;
    hp	   += int_node_size;
#else
    r = (Node *)(int_val(sp[1]) * ((long)sp[0] - 1) + 1);
    sp += 2;
#endif
    RETURN(r);
}

DECLARE_ENTRYPOINT(__div);
DECLARE_LABEL(__div_1);

FUNCTION(__div)
{
    Node *aux;

    EXPORT_LABEL(__div)
 ENTRY_LABEL(__div)
    EVAL_RIGID_INT(__div);
    aux   = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(__div_1);
}

static
FUNCTION(__div_1)
{
    int  i;
    Node *r;

 ENTRY_LABEL(__div_1)
    EVAL_RIGID_INT(__div_1);
    i	= int_val(sp[1]) / int_val(sp[0]);
    sp += 2;

#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = i;
    hp	   += int_node_size;
#else
    r = mk_int(i);
#endif
    RETURN(r);
}


DECLARE_ENTRYPOINT(__mod);
DECLARE_LABEL(__mod_1);

FUNCTION(__mod)
{
    Node *aux;

    EXPORT_LABEL(__mod)
 ENTRY_LABEL(__mod)
    EVAL_RIGID_INT(__mod);
    aux   = sp[0];
    sp[0] = sp[1];
    sp[1] = aux;
    GOTO(__mod_1);
}

static
FUNCTION(__mod_1)
{
    int  i;
    Node *r;

 ENTRY_LABEL(__mod_1)
    EVAL_RIGID_INT(__mod_1);
    i	= int_val(sp[1]) % int_val(sp[0]);
    sp += 2;

#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = i;
    hp	   += int_node_size;
#else
    r = mk_int(i);
#endif
    RETURN(r);
}
