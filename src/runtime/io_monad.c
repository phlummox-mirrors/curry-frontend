#line 29 "io_monad.nw"
#include "curry.h"

DECLARE_LABEL(start_io);
DECLARE_LABEL(stop_io);
DECLARE_LABEL(choices_io);
DECLARE_LABEL(deadlock_io);
DECLARE_LABEL(fail_io);

static void fail_with(const char *msg) __attribute__((noreturn));

#line 48 "io_monad.nw"
static struct nondet_handlers io_handlers = {
    choices_io, deadlock_io, fail_io
};

static
FUNCTION(choices_io)
{
 ENTRY_LABEL(choices_io)
    fail_with("ERROR: Cannot duplicate the world");
}

static
FUNCTION(deadlock_io)
{
 ENTRY_LABEL(deadlock_io)
    fail_with("Suspended");
}

static
FUNCTION(fail_io)
{
 ENTRY_LABEL(fail_io)
    fail_with("Failed");
}

#line 103 "io_monad.nw"
static int  curry_argc;
static char **curry_argv;
static int  curry_rc = 0;

int
curry_exec(FunctionInfo *main_info_table, int argc, char **argv)
{
    struct closure_node main_function;

    curry_argc = argc;
    curry_argv = argv;

    CHECK_STACK1();
    main_function.info = main_info_table;
    *--sp = (Node *)&main_function;

    run(start_io);
    return curry_rc;
}

void
curry_exit(int rc)
{
    curry_rc = rc;
    halt();
}

static
FUNCTION(start_io)
{
 ENTRY_LABEL(start_io)
    nondet_handlers = io_handlers;
    TRACE(("start program\n"));
    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = sp[2];
    sp[1] = unit;
    sp[2] = (Node *)0;
    start_thread(3);
    /* Hack: Change the return address of the main thread */
    sp[2] = (Node *)stop_io;
    GOTO(___64_);
}

static
FUNCTION(stop_io)
{
 ENTRY_LABEL(stop_io)
    curry_exit(0);
}

static void
fail_with(const char *msg)
{
    fprintf(stderr, "%s\n", msg);
    curry_exit(1);
}

#line 169 "io_monad.nw"
Node *
getProgName()
{
    return from_string(curry_argv[0]);
}

Node *
getArgs()
{
    unsigned i = curry_argc;
    Node     *arg, *cons = nil;
    ADD_LOCAL_ROOTS1((Node *)0);
#define tail LOCAL_ROOT[0]

    while ( i-- > 1 )
    {
	/* NB: from_string may invoke gc; only tail is preserved here */ 
	tail		= cons;
	arg		= from_string(curry_argv[i]);
	cons		= (Node *)hp;
	cons->info	= &cons_info;
	cons->c.args[0] = arg;
	cons->c.args[1] = tail;
	hp	       += cons_node_size;
    }

#undef tail
    DROP_LOCAL_ROOTS();
    return cons;
}

#line 211 "io_monad.nw"
DECLARE_ENTRYPOINT(__done);

FUNCTION(__done)
{
    EXPORT_LABEL(__done)
 ENTRY_LABEL(__done)
    sp += 1;
    RETURN(unit);
}

DECLARE_ENTRYPOINT(__return);

FUNCTION(__return)
{
    Node *r;

    EXPORT_LABEL(__return)
 ENTRY_LABEL(__return)
    r	= sp[0];
    sp += 2;
    RETURN(r);
}

DECLARE_ENTRYPOINT(___62__62_);
DECLARE_LABEL(___62__62_1);

FUNCTION(___62__62_)
{
    EXPORT_LABEL(___62__62_)
 ENTRY_LABEL(___62__62_)
    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = sp[2];
    sp[1] = sp[4];
    sp[2] = (Node *)___62__62_1;
    GOTO(___64_);
}

static
FUNCTION(___62__62_1)
{
 ENTRY_LABEL(___62__62_1)
    sp += 1;
    GOTO(___64_);
}

DECLARE_ENTRYPOINT(___62__62__61_);
DECLARE_LABEL(___62__62__61_1);
DECLARE_LABEL(___62__62__61_2);

FUNCTION(___62__62__61_)
{
    EXPORT_LABEL(___62__62__61_)
 ENTRY_LABEL(___62__62__61_)
    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = sp[2];
    sp[1] = sp[4];
    sp[2] = (Node *)___62__62__61_1;
    GOTO(___64_);
}

static
FUNCTION(___62__62__61_1)
{
 ENTRY_LABEL(___62__62__61_1)
    CHECK_STACK1();
    sp -= 1;
    sp[0] = sp[2];
    sp[2] = (Node *)___62__62__61_2;
    GOTO(___64_);
}

static
FUNCTION(___62__62__61_2)
{
 ENTRY_LABEL(___62__62__61_2)
    GOTO(___64_);
}

#line 301 "io_monad.nw"
DECLARE_ENTRYPOINT(__catch);
DECLARE_LABEL(__catch_1);

FUNCTION(__catch)
{
    Node	   *action, *handler, *world;
    ExceptionFrame *prevFrame;

    EXPORT_LABEL(__catch)
 ENTRY_LABEL(__catch)

    CHECK_STACK(wordsof(ExceptionFrame));
    action  = sp[0];
    handler = sp[1];
    world   = sp[2];

    /* create and initialize the new exception frame */
    sp += 3 - wordsof(ExceptionFrame);
    prevFrame	 = efp;
    efp		 = (ExceptionFrame *)sp;
    efp->handler = handler;
    efp->frame	 = prevFrame;

    /* invoke the action */
    sp -= 3;
    sp[0] = action;
    sp[1] = world;
    sp[2] = (Node *)__catch_1;
    GOTO(___64_);
}

static
FUNCTION(__catch_1)
{
    Node	   *r;
    ExceptionFrame *curFrame;

 ENTRY_LABEL(__catch_1)
    r = sp[0];

    curFrame = efp;
    efp	     = efp->frame;
    sp	     = (Node **)curFrame + wordsof(ExceptionFrame);

    RETURN(r);
}

#line 357 "io_monad.nw"
DECLARE_ENTRYPOINT(__prelude__error);
DECLARE_LABEL(__ioError_1);

FUNCTION(__ioError)
{
    Node	   *exc, *handler, *world;
    ExceptionFrame *curFrame;

    EXPORT_LABEL(__ioError)
 ENTRY_LABEL(__ioError)
    TRACE(("%I throw %N\n", sp[0]));

    if ( efp == (ExceptionFrame *)0 )
    {
	sp[1] = prefix_string("Uncaught I/O exception:\n", sp[0]);
	sp   += 1;
	GOTO(__prelude__error);
    }

    exc	     = sp[0];
    world    = sp[1];
    curFrame = efp;
    handler  = efp->handler;
    efp	     = efp->frame;

    sp    = (Node **)curFrame + wordsof(ExceptionFrame) - 4;
    sp[0] = handler;
    sp[1] = exc;
    sp[2] = (Node *)__ioError_1;
    sp[3] = world;
    GOTO(___64_);
}

static
FUNCTION(__ioError_1)
{
 ENTRY_LABEL(__ioError_1)
    GOTO(___64_);
}

#line 410 "io_monad.nw"
DECLARE_ENTRYPOINT(__unsafePerformIO);
DECLARE_LABEL(__unsafePerformIO_1);

FUNCTION(__unsafePerformIO)
{
    EXPORT_LABEL(__unsafePerformIO)
 ENTRY_LABEL(__unsafePerformIO)
    CHECK_STACK(2);
    sp	 -= 2;
    sp[0] = sp[2];
    sp[1] = unit;
    sp[2] = (Node *) __unsafePerformIO_1;
    GOTO(___64_);
}

static
FUNCTION(__unsafePerformIO_1)
{
    Node *r;

 ENTRY_LABEL(__unsafePerformIO_1)
    r = sp[0];
    if ( is_boxed(r) )
	GOTO(r->info->eval);
    sp += 1;
    RETURN(r);
}

#line 464 "io_monad.nw"
DECLARE_ENTRYPOINT(__fixIO);

FUNCTION(__fixIO)
{
    Node *clos, *clos2, *susp;
    EXPORT_LABEL(__fixIO)
 ENTRY_LABEL(__fixIO)
    CHECK_HEAP(2*closure_node_size(2) + suspend_node_size);
    clos  = (Node *)hp;
    clos2 = (Node *)(hp + closure_node_size(2));
    susp  = (Node *)(hp + 2*closure_node_size(2));
    hp   += 2*closure_node_size(2) + suspend_node_size;

    clos->cl.info    = &___64__info;
    clos->cl.args[0] = sp[0];
    clos->cl.args[1] = susp;

    clos2->cl.info    = &___64__info;
    clos2->cl.args[0] = clos;
    clos2->cl.args[1] = sp[1];

    susp->s.info = &___64__suspend_info;
    susp->s.fn	 = clos2;
    susp->s.spc	 = ss;
    hp		+= suspend_node_size;

    *++sp = susp;
    GOTO(susp->info->eval);    
}

#line 498 "io_monad.nw"
DECLARE_ENTRYPOINT(__performGC);

FUNCTION(__performGC)
{
    EXPORT_LABEL(__performGC)
 ENTRY_LABEL(__performGC)
    sp += 1;
    collect(0);
    RETURN(unit);
}
