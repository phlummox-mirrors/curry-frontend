#line 12 "system.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/wait.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "eval.h"
#include "cstring.h"
#include "cam.h"
#include "io_monad.h"
#include "trace.h"

#line 33 "system.nw"
DECLARE_ENTRYPOINT(__getProgName);

FUNCTION(__getProgName)
{
    Node *r;

    EXPORT_LABEL(__getProgName)
 ENTRY_LABEL(__getProgName)
    sp += 1;
    r	= getProgName();
    RETURN(r);
}

#line 51 "system.nw"
DECLARE_ENTRYPOINT(__getArgs);

FUNCTION(__getArgs)
{
    Node *r;

    EXPORT_LABEL(__getArgs)
 ENTRY_LABEL(__getArgs)
    sp += 1;
    r	= getArgs();
    RETURN(r);
}

#line 70 "system.nw"
DECLARE_ENTRYPOINT(__getEnv);

DECLARE_LABEL(__getEnv_1);

FUNCTION(__getEnv)
{
    EXPORT_LABEL(__getEnv)
 ENTRY_LABEL(__getEnv)
    CHECK_STACK1();
    sp	 -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__getEnv_1;
    GOTO(nf_string);
}

static
FUNCTION(__getEnv_1)
{
    char *var, *val;
    Node *r;

 ENTRY_LABEL(__getEnv_1)
    var = to_string(sp[0]);
    val = getenv(var);
    free(var);
    if ( val == (char *)0 )
    {
	sp[0] = prefix_string("environment variable not set: ", sp[0]);
	GOTO(__ioError);
    }

    sp += 2;
    r	= from_string(val);
    RETURN(r);
}

#line 111 "system.nw"
DECLARE_ENTRYPOINT(__system);

DECLARE_LABEL(__system_1);

FUNCTION(__system)
{
    EXPORT_LABEL(__system)
 ENTRY_LABEL(__system)
    CHECK_STACK1();
    sp -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__system_1;
    GOTO(nf_string);
}

static
FUNCTION(__system_1)
{
    int  res;
    char *cmd;
    Node *r;

 ENTRY_LABEL(__system_1)
    cmd = to_string(sp[0]);
    res = system(cmd);
    free(cmd);
    if ( res == -1 )
    {
	sp[0] = from_string(strerror(errno));
	GOTO(__ioError);
    }
    
    sp += 2;
    if ( WIFSIGNALED(res) )
	res = -WTERMSIG(res);
    else
    {
	ASSERT(WIFEXITED(res));
	res = WEXITSTATUS(res);
    }

#if !ONLY_BOXED_OBJECTS
    r = mk_int(res);
#else
    CHECK_HEAP(int_node_size);
    r	      = (Node *)hp;
    r->i.info = &int_info;
    r->i.i    = res;
    hp	     += int_node_size;
#endif
    RETURN(r);
}

#line 170 "system.nw"
DECLARE_ENTRYPOINT(__curryExit);

FUNCTION(__curryExit)
{
    EXPORT_LABEL(__curryExit)
 ENTRY_LABEL(__curryExit)
    EVAL_RIGID_INT(__curryExit);
    curry_exit(int_val(sp[0]));
}
