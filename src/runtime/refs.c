#line 13 "refs.nw"
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

enum { IOREF_TAG };

struct ioref_node {
    NodeInfo *info;
    Node     *ref;
};

#define ioref_node_size wordsof(struct ioref_node)

static NodeInfo ioref_info = {
    IOREF_TAG, ioref_node_size, (const int *)0, (Label)eval_whnf, "IORef",
    (FinalFun)0
};

#line 46 "refs.nw"
DECLARE_ENTRYPOINT(__newIORef);

FUNCTION(__newIORef)
{
    struct ioref_node *ref;

    EXPORT_LABEL(__newIORef)
 ENTRY_LABEL(__newIORef)
    CHECK_HEAP(ioref_node_size);
    ref	      = (struct ioref_node *)hp;
    ref->info = &ioref_info;
    ref->ref  = sp[0];
    hp	     += ioref_node_size;
    
    sp += 2;
    RETURN((Node *)ref);
}

#line 71 "refs.nw"
DECLARE_ENTRYPOINT(__readIORef);

FUNCTION(__readIORef)
{
    struct ioref_node *ref;

   EXPORT_LABEL(__readIORef)
 ENTRY_LABEL(__readIORef)
    EVAL_RIGID(__readIORef);
    ASSERT(node_tag(sp[0]) == IOREF_TAG);
    ref = (struct ioref_node *)sp[0];
    sp += 2;
    RETURN(ref->ref);
}

#line 96 "refs.nw"
DECLARE_ENTRYPOINT(__writeIORef);

FUNCTION(__writeIORef)
{
    struct ioref_node *ref;

    EXPORT_LABEL(__writeIORef)
 ENTRY_LABEL(__writeIORef)
    EVAL_RIGID(__writeIORef);
    ASSERT(node_tag(sp[0]) == IOREF_TAG);
    ref = (struct ioref_node *)sp[0];
    SAVE(ref, ref);
    ref->ref = sp[1];
    sp += 3;
    RETURN(unit);
}
