#line 29 "backtrack.nw"
#include "curry.h"
#include <unistd.h>
#include <ctype.h>
#include "print.h"
#include "vars.h"
#include "stats.h"

static void push_choicepoint(Label *);

DECLARE_LABEL(start);
DECLARE_LABEL(stop);
DECLARE_LABEL(choices);
DECLARE_LABEL(fail);

#line 52 "backtrack.nw"
static struct nondet_handlers global_handlers = { choices, stop, fail };

static void
push_choicepoint(Label *alts)
{
    Choicepoint	       *oldBp = bp;
    const unsigned int cp_sz  = wordsof(Choicepoint);
    const unsigned int stk_sz =
	(bp != (Choicepoint *)0 ? (Node **)bp : stack_end) - sp;

    /* create a new choicepoint on the stack */
    CHECK_STACK(cp_sz + stk_sz);
    bp		 = (Choicepoint *)(sp - cp_sz);
    bp->btAlts	 = alts;
    bp->btCid	 = cid;
    bp->btDsBase = ds_base;
    bp->btBp	 = oldBp;
    bp->btRq	 = rq;
    bp->btTp	 = tp;
    bp->btDict	 = names_tail;
    bp->btHp	 = hp;

    /* copy the current thread to the top of the stack */
    memcpy(sp - cp_sz - stk_sz, sp, stk_sz*word_size);
    sp	    -= cp_sz + stk_sz;
    ds_base -= cp_sz + stk_sz;

    /* adjust the trail limit */
    hlim = hp;
}

static
FUNCTION(choices)
{
 ENTRY_LABEL(choices)

    TRACE(("%I try\n"));

    /* create a new choicepoint on the control stack */
    push_choicepoint(choice_conts + 1);

    /* continue at the first alternative */
    GOTO(choice_conts[0]);
}

static
FUNCTION(fail)
{
    unsigned int stk_sz;
    Label	 *choice_conts;

 ENTRY_LABEL(fail)

    TRACE(("%I fail\n"));

    /* if no alternatives are available terminate the program */
    if ( bp == (Choicepoint *)0 )
    {
	ASSERT(cid != 0);
	halt();
    }

    /* restore the old bindings from the trail */
    RESTORE(bp->btTp);

    /* restore registers from the choicepoint */
    cid	    = bp->btCid;
    ds_base = bp->btDsBase;
    rq	    = bp->btRq;

    /* release the memory allocated since the last choicepoint */
    release_names(bp->btDict);
    release_mem();

    /* if only one alternative remains, drop the choicepoint */
    choice_conts = bp->btAlts;
    ASSERT(choice_conts[0] != (Label)0);
    if ( choice_conts[1] == (Label)0 )
    {
	TRACE(("%I trust\n"));
	sp   = (Node **)bp + wordsof(Choicepoint);
	bp   = bp->btBp;
	hlim = bp == (Choicepoint *)0 ? (word *)0 : bp->btHp;
    }

    /* otherwise update the choicepoint */
    else
    {
	TRACE(("%I retry\n"));
	bp->btAlts = choice_conts + 1;

	/* copy the stack */
	stk_sz =
	    (bp->btBp != (Choicepoint *)0 ? (Node **)bp->btBp : stack_end)
		- (Node **)(bp + 1);
	sp       = (Node **)bp - stk_sz;
	ds_base -= wordsof(Choicepoint) + stk_sz;
	memcpy(sp, sp + wordsof(Choicepoint) + stk_sz, stk_sz * word_size);
    }

    /* continue at the next alternative */
    GOTO(choice_conts[0]);
}

#line 196 "backtrack.nw"
static Node    *eval_apply(FunctionInfo *, const char **);
static Node    *eval_first(Node *);
static Node    *eval_next();
static boolean eval_continue(boolean *);
static void    bad_usage(const char *) __attribute__((noreturn));

static void
bad_usage(const char *pname)
{
    fprintf(stderr, "usage: %s [-i|-n]\n", pname);
    fprintf(stderr, " -i\tforce interactive mode\n");
    fprintf(stderr, " -n\tforce non-interactive mode\n");
    exit(1);
}

int
curry_eval(FunctionInfo *goal_info_table, const char *fv_names[],
	   int argc, char **argv)
{
    int	    opt;
    boolean first = true, interactive;
    Node    *susp;
    ADD_LOCAL_ROOTS1((Node *)0);
#define goal LOCAL_ROOT[0]

    /* check if process is connected to a terminal */
    interactive = isatty(0) == 1;

    /* process command line options */
    while ( (opt = getopt(argc, argv, "in")) != EOF )
	switch ( opt )
	{
	case 'i':
	    interactive = true;
	    break;
	case 'n':
	    interactive = false;
	    break;
	default:
	    fprintf(stderr, "%s: unknown option -%c\n", argv[0], opt);
	    bad_usage(argv[0]);
	}

    if ( optind != argc )
    {
	fprintf(stderr, "%s: too many arguments\n", argv[0]);
	bad_usage(argv[0]);
    }

    /* evaluate goal */
    goal = eval_apply(goal_info_table, fv_names);
    susp = eval_first(goal);
    if ( susp != (Node *)0 )
	for ( ;; )
	{
	    if ( !interactive )
	    {
		if ( first )
		    first = false;
		else
		    printf(" | ");
	    }
	    if ( is_indir_node(susp) )
		print_result(fv_names, goal->cl.args + 1, goal->cl.args[0]);
	    else
		printf("Suspended");

	    if ( !eval_continue(&interactive) )
		break;

	    susp = eval_next();
	    if ( susp == (Node *)0 )
	    {
		printf("%s\n", interactive ? "No more solutions" : "");
		break;
	    }
	}
    else
	fprintf(interactive ? stdout : stderr, "No solution\n");
#undef goal
    DROP_LOCAL_ROOTS();
    return 0;
}

static Node *
eval_apply(FunctionInfo *goal_info_table, const char *fv_names[])
{
    unsigned int	 i, n;
    const char		 **fv;
    Node		 *clos, *var;
    struct variable_node *vars;

    for ( n = 0, fv = fv_names; *fv != (const char *)0; n++, fv++ )
	;
    ASSERT(goal_info_table[0].arity == n + 1);

    CHECK_HEAP(closure_node_size(n + 1) + (n + 1) * variable_node_size);
    vars = (struct variable_node *)hp;
    for ( i = 0; i <= n; i++ )
    {
	var	     = (Node *)hp;
	var->info    = &variable_info;
	var->v.cstrs = (Constraint *)0;
	var->v.wq    = (ThreadQueue)0;
	var->v.spc   = ss;
	hp	    += variable_node_size;
    }

    clos	  = (Node *)hp;
    clos->cl.info = goal_info_table + n + 1;
    for ( i = 0; i <= n; i++ )
	clos->cl.args[i] = (Node *)(vars + i);
    hp += closure_node_size(n + 1);

    for ( i = 0; i < n; i++ )
	add_name((Node *)(vars + i + 1), fv_names[i]);

    return clos;
}

static Node *
eval_first(Node *goal)
{
    Node *susp;

    CHECK_HEAP(queueMe_node_size);
    susp	= (Node *)hp;
    susp->info	= &queueMe_info;
    susp->q.wq	= (ThreadQueue)0;
    susp->q.spc	= ss;
    hp	       += queueMe_node_size;

    sp	  = stack_end - 2;
    sp[0] = goal;
    sp[1] = susp;

    run(start);
    return cid == 0 ? stack_end[-1] : (Node *)0;
}

static Node *
eval_next()
{
    run(fail);
    return cid == 0 ? stack_end[-1] : (Node *)0;
}

static boolean
eval_continue(boolean *interactive)
{
    int c, c1;

    /* terminate the program if no alternatives remain */
    if ( bp == (Choicepoint *)0 )
    {
	printf("\n");
	return false;
    }

    if ( *interactive )
    {
	printf("\nMore solutions? [Y(es)/n(o)/a(ll)] ");
	fflush(stdout);
	c = getchar();
	while ( c != EOF && c != '\n' && isspace(c) )
	    c = getchar();
	for ( c1 = c; c1 != EOF && c1 != '\n'; )
	    c1 = getchar();
	if ( c1 == EOF )
	    printf("\n");

	if ( c == 'n' || c == 'N' || c == EOF )
	    return false;
	else if ( c == 'a' || c == 'A' )
	    *interactive = false;
    }
    else
	fflush(stdout);

    /* backtrack to the next solution */
    return true;
}

static
FUNCTION(start)
{
    Node  *susp, *goal;
    Label eval;
 ENTRY_LABEL(start)
    nondet_handlers = global_handlers;
    TRACE(("start program\n"));

    goal = sp[0];
    susp = sp[1];
    eval = goal->info->eval;

    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = goal;
    sp[1] = (Node *)update;
    sp[2] = susp;
    sp[3] = (Node *)0;
    start_thread(4);
    GOTO(eval);
}

static
FUNCTION(stop)
{
 ENTRY_LABEL(stop)
    cid = 0;
    halt();
}
