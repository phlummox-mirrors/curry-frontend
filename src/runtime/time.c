#line 12 "time.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <time.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "eval.h"
#include "cstring.h"
#include "io_monad.h"
#include "cam.h"
#include "trace.h"

#line 36 "time.nw"
DECLARE_ENTRYPOINT(__getClockTime);

FUNCTION(__getClockTime)
{
    time_t tim;
    Node   *r;
    EXPORT_LABEL(__getClockTime)
 ENTRY_LABEL(__getClockTime)

    if ( time(&tim) == (time_t)-1 )
    {
	CHECK_STACK1();
        r     = from_string(strerror(errno));
	*--sp = r;
	GOTO(__ioError);
    }

    sp += 1;
#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = tim;
    hp	   += int_node_size;
#else
    r = mk_int(tim);
#endif
    RETURN(r);
}
