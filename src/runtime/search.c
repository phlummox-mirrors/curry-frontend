#line 19 "search.nw"
#include "curry.h"
#include "search.h"
#include "vars.h"
#include "stats.h"

static void push_search_context(void);
static void pop_search_context(void);

DECLARE_LABEL(solved_goal_code);
DECLARE_LABEL(solved_goal_code_eval);
DECLARE_LABEL(search_cont_code);
DECLARE_LABEL(search_cont_code_eval);
DECLARE_LABEL(search_goal_proceed);
DECLARE_LABEL(resume_search);
DECLARE_LABEL(choices_search);
DECLARE_LABEL(deadlock_search);
DECLARE_LABEL(fail_search);

static struct nondet_handlers search_handlers = {
    choices_search, deadlock_search, fail_search
};

struct context {
    SearchSpace		   *spc;
    struct nondet_handlers handlers;
};

#line 54 "search.nw"
static void
push_search_context()
{
    Choicepoint	   *oldBp = bp;
    struct context *ctxt;

    CHECK_STACK(wordsof(Choicepoint) + wordsof(struct context));
    sp   -= wordsof(Choicepoint) + wordsof(struct context);
    sp[0] = sp[wordsof(Choicepoint) + wordsof(struct context)];

    /* allocate a new search context on the stack */
    bp		   = (Choicepoint *)(sp + 1);
    bp->btAlts	   = (Label *)0; /* btAlts == 0 identifies search context */
    bp->btCid	   = cid;
    bp->btDsBase   = ds_base;
    bp->btBp	   = oldBp;
    bp->btRq	   = rq;
    bp->btTp	   = tp;
    bp->btDict	   = names_tail;
    bp->btHp	   = hp;

    /* save the current search space */
    ctxt      = (struct context *)(bp + 1);
    ctxt->spc = ss;

    /* change the current handler vector */
    memcpy(&ctxt->handlers, &nondet_handlers, sizeof(nondet_handlers));
    nondet_handlers = search_handlers;

    /* initialize the machine state for the new context */
    cid	    = 0;
    ds_base = sp;
    rq	    = (ThreadQueue)0;
    hlim    = hp;
}

static void
pop_search_context()
{
    Choicepoint	   *oldBp = bp;
    struct context *ctxt;

    ASSERT(oldBp->btAlts == (Label *)0);

    /* restore the old handler vector */
    ctxt = (struct context *)(bp + 1);
    memcpy(&nondet_handlers, &ctxt->handlers, sizeof(nondet_handlers));

    /* restore the old search space */
    ss = ctxt->spc;

    /* restore the machine state from the current search context */
    cid	    = oldBp->btCid;
    ds_base = oldBp->btDsBase;
    bp	    = oldBp->btBp;
    rq	    = oldBp->btRq;
    tp	    = oldBp->btTp;
    hlim    = bp != (Choicepoint *)0 ? bp->btHp : heap_base;
    sp	    = (Node **)(oldBp + 1) + wordsof(struct context);
}

#line 122 "search.nw"
DECLARE_ENTRYPOINT(__try);

FUNCTION(__try)
{
    Node *susp, *list, *sc, *var;

    EXPORT_LABEL(__try)
 ENTRY_LABEL(__try)
    EVAL_RIGID(__try);

    ASSERT(is_papp_node(sp[0]) &&
	   closure_argc(sp[0]) + 1 == sp[0]->cl.info->arity);

    /* return immediately when applied to a solved search goal */
    if ( sp[0]->cl.info->entry == solved_goal_code )
    {
	CHECK_HEAP(cons_node_size);
	list		= (Node *)hp;
	list->c.info	= &cons_info;
	list->c.args[0] = *sp++;
	list->c.args[1] = nil;
	hp	       += cons_node_size;
	RETURN(list);
    }

    /* create a new search context */
    TRACE(("starting encapsulated search\n"));
    push_search_context();

    /* when applied to a search continuation continue it */
    if ( sp[0]->cl.info->entry == search_cont_code )
    {
	sc    = sp[0]->cl.args[0];
	sp[0] = sc;   
	new_search_space(sc->sc.spc);

	CHECK_STACK(1);
	sp   -= 1;
	sc    = sp[1];
	sp[0] = sc->sc.susp;
	sp[1] = sc->sc.var;
	GOTO(resume_continuation(sc));
    }

    /* create a new search space */
    new_search_space((SearchSpace *)0);

    /* allocate new goal variable and suspension */
    CHECK_HEAP(variable_node_size + queueMe_node_size);
    var		 = (Node *)hp;
    var->info	 = &variable_info;
    var->v.cstrs = (Constraint *)0;
    var->v.wq	 = (ThreadQueue)0;
    var->v.spc	 = ss;
    hp		+= variable_node_size;

    susp	= (Node *)hp;
    susp->info	= &queueMe_info;
    susp->q.wq	= (ThreadQueue)0;
    susp->q.spc	= ss;
    hp	       += queueMe_node_size;

    /* start the initial thread and evaluate the goal */
    CHECK_STACK(6);
    sp	 -= 6;
    sp[0] = sp[6];
    sp[1] = var;
    sp[2] = (Node *)update;
    sp[3] = susp;
    sp[4] = (Node *)0;
    sp[5] = susp;
    sp[6] = var;
    start_thread(5);
    GOTO(___64_);
}

static
FUNCTION(solved_goal_code_eval)
{
    Node *clos;
 ENTRY_LABEL(solved_goal_code_eval)
    CHECK_STACK1();
    clos  = sp[0];
    sp	 -= 1;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    GOTO(solved_goal_code);
}

static
FUNCTION(solved_goal_code)
{
    Node  *cont, *res, *arg;
    Label ret_ip;

 ENTRY_LABEL(solved_goal_code)
    cont = sp[0];
    res	 = copy_graph(cont->sc.var, cont->sc.spc);

    arg = sp[1];
    while ( is_boxed(arg) && arg->info->tag == INDIR_TAG )
	arg = arg->n.node;
    if ( is_boxed(arg) && is_variable_node(arg) && is_local_space(arg->v.spc) )
    {
	sp    += 2;
	ret_ip = (Label)sp[0];
	sp[0]  = Success;
	GOTO(bind_var(arg, res, ret_ip));
    }

    sp[0] = arg;
    sp[1] = res;
    GOTO(___61__58__61_);
}

static
FUNCTION(search_cont_code_eval)
{
    Node *clos;
 ENTRY_LABEL(search_cont_code_eval)
    CHECK_STACK1();
    clos  = sp[0];
    sp	 -= 1;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    GOTO(search_cont_code);
}

static
FUNCTION(search_cont_code)
{
    Node *arg, *cont;

 ENTRY_LABEL(search_cont_code)

    cont = sp[0];
    if ( !inject_search_space(cont->sc.spc) )
	cont = copy_graph(cont, cont->sc.spc);
    restore_continuation(cont);

    arg = sp[1];
    while ( is_boxed(arg) && arg->info->tag == INDIR_TAG )
	arg = arg->n.node;
    if ( is_boxed(arg) && is_variable_node(arg) && is_local_space(arg->v.spc) )
    {
	sp[0] = Success;
	sp[1] = cont->sc.susp;
	GOTO(bind_var(arg, cont->sc.var, search_goal_proceed));
    }

    CHECK_STACK(2);
    sp   -= 2;
    sp[0] = arg;
    sp[1] = cont->sc.var;
    sp[2] = (Node *)search_goal_proceed;
    sp[3] = cont->sc.susp;
    GOTO(___61__58__61_);
}

static
FUNCTION(search_goal_proceed)
{
    Node *susp;

 ENTRY_LABEL(search_goal_proceed)
    sp	+= 1;
    susp = sp[0];
    ASSERT(is_boxed(susp));
    GOTO(susp->info->eval);
}

#line 309 "search.nw"
static
FUNCTION(deadlock_search)
{
    Node **ds_base, *goal, *sc, *list, *solved_cont;
    static FunctionInfo solved_goal_info_table[] = {
	PAPPINFO("<solved goal>", 1, solved_goal_code, 2)
	FUNINFO("<solved goal>",     solved_goal_code, 2)
    };

 ENTRY_LABEL(deadlock_search)

    ds_base = (Node **)bp - 2;
    for ( goal = ds_base[0]; ; )
    {
	switch ( goal->info->tag )
	{
	case INDIR_TAG:
	    goal = goal->n.node;
	    continue;
	case SUSPEND_TAG:
	    fprintf(stderr, "search goal not locked\n");
	    exit(2);
	case QUEUEME_TAG:
	case VARIABLE_TAG:
	    TRACE(("deadlock in encapsulated search\n"));
	    discard_search_space();
	    pop_search_context();
	    GOTO(stop_thread);
	default:
	    break;
	}
	break;
    }

    TRACE(("leaving encapsulated search with solved search goal\n"));
    while ( is_boxed(ds_base[1]) && ds_base[1]->info->tag == INDIR_TAG )
	ds_base[1] = ds_base[1]->n.node;
    save_search_space();

    CHECK_HEAP(search_cont_node_size + closure_node_size(1) + cons_node_size);
    sc		= (Node *)hp;
    sc->sc.info	= &search_cont_info;
    sc->sc.code	= (Label)0;
    sc->sc.susp	= (Node *)0;
    sc->sc.var	= ds_base[1];
    sc->sc.ds	= (Node *)0;
    sc->sc.rq	= (ThreadQueue)0;
    sc->sc.spc	= ss;
    hp	       += search_cont_node_size;

    solved_cont		    = (Node *)hp;
    solved_cont->cl.info    = solved_goal_info_table;
    solved_cont->cl.args[0] = sc;
    hp			   += closure_node_size(1);

    list	    = (Node *)hp;
    list->c.info    = &cons_info;
    list->c.args[0] = solved_cont;
    list->c.args[1] = nil;
    hp		   += cons_node_size;

    pop_search_context();
    RETURN(list);
}

#line 383 "search.nw"
Label
suspend_search(Label retIp, Node *node, enum suspend_reason reason)
{
    Node **ds_base, *sc;
    ADD_LOCAL_ROOTS1(node);

    TRACE(("suspending encapsulated search\n"));

    /* dereference the goal nodes in order to avoid some garbage */
    ds_base = (Node **)bp - 2;
    while ( is_boxed(ds_base[0]) && ds_base[0]->info->tag == INDIR_TAG )
	ds_base[0] = ds_base[0]->n.node;
    while ( is_boxed(ds_base[1]) && ds_base[1]->info->tag == INDIR_TAG )
	ds_base[1] = ds_base[1]->n.node;

    /* leave the current search space */
    save_search_space();
    sc		= save_continuation(retIp, ds_base);
    sc->sc.susp = ds_base[0];
    sc->sc.var	= ds_base[1];
    pop_search_context();

    /* save the search continuation, the search space we return to,
     * and the variable/suspension which caused suspension */
#define node LOCAL_ROOT[0]
    CHECK_STACK(4);
    sp   -= 3;
    sp[2] = sc;
    sp[1] = (Node *)ss;
    sp[0] = node;
    DROP_LOCAL_ROOTS();
#undef node

    /* either evaluate the node on the top of the stack or delay the thread */
    switch ( reason )
    {
    case Eval:
	sp   -= 1;
	sp[0] = sp[1];
	sp[1] = (Node *)resume_search;
    	return sp[0]->info->eval;
    case Delay:
	return delay_thread(resume_search, sp[0]);
    default:
	fprintf(stderr, "suspend_search: unexpected reason %d\n", reason);
	exit(1);
    }
}

#line 444 "search.nw"
static
FUNCTION(resume_search)
{
    boolean do_resume;
    Node    *sc;

 ENTRY_LABEL(resume_search)
    ASSERT(is_boxed(sp[2]) && is_search_cont_node(sp[2]));

    do_resume = ss == (SearchSpace *)sp[1] && (word *)sp[2] >= hlim;
    sp	     += 2;

    push_search_context();
    CHECK_STACK(2);
    sc	  = sp[0];
    sp	 -= 2;
    sp[0] = sc;
    sp[1] = sc->sc.susp;
    sp[2] = sc->sc.var;

    if ( do_resume )
	resume_search_space(sc->sc.spc);
    else
	new_search_space(sc->sc.spc);

    TRACE(("resuming encapsulated search\n"));
    GOTO(resume_continuation(*sp++));
}

#line 480 "search.nw"
static
FUNCTION(choices_search)
{
    unsigned int n_conts;
    Node	 **ds_base, *list, *cons, *clos, *sc;
    Label	 *conts;
    static FunctionInfo search_cont_info_table[] = {
	PAPPINFO("<search goal>", 1, search_cont_code, 2)
	FUNINFO("<search goal>",     search_cont_code, 2)
    };

 ENTRY_LABEL(choices_search)

    ASSERT(bp != (Choicepoint *)0 && is_search_context(bp));

    /* compute the number of alternative solutions */
    n_conts = 0;
    for ( conts = choice_conts; *conts != (Label)0; conts++ )
	n_conts++;
    ASSERT(n_conts > 1);

    TRACE(("leaving encapsulated search with %u continuations\n", n_conts));

    /* dereference the goal nodes in order to avoid some garbage */
    ds_base = (Node **)bp - 2;
    while ( is_boxed(ds_base[0]) && ds_base[0]->info->tag == INDIR_TAG )
	ds_base[0] = ds_base[0]->n.node;
    while ( is_boxed(ds_base[1]) && ds_base[1]->info->tag == INDIR_TAG )
	ds_base[1] = ds_base[1]->n.node;

    /* create a search continuation and leave the current search space */
    save_search_space();
    sc		= save_continuation(*--conts, ds_base);
    sc->sc.susp = ds_base[0];
    sc->sc.var	= ds_base[1];
    pop_search_context();

    /* allocate the list of search continuations */
    *--sp = sc;
    CHECK_HEAP(n_conts * (cons_node_size + closure_node_size(1))
	       + (n_conts - 1) * search_cont_node_size);

    sc	 = *sp++;
    list = nil;
    while ( n_conts-- > 0 )
    {
	clos		 = (Node *)hp;
	clos->cl.info	 = search_cont_info_table;
	clos->cl.args[0] = sc;
	hp		+= closure_node_size(1);

	cons		= (Node *)hp;
	cons->info	= &cons_info;
	cons->c.args[0] = clos;
	cons->c.args[1] = list;
	hp	       += cons_node_size;
	list		= cons;

	if ( n_conts > 0 )
	{
	    memcpy(hp, sc, search_cont_node_size * word_size);
	    sc		= (Node *)hp;
	    sc->sc.code = *--conts;
	    hp	       += search_cont_node_size;
	}
    }
    ASSERT(conts == choice_conts);

    /* return the list */
    RETURN(list);
}

static
FUNCTION(fail_search)
{
 ENTRY_LABEL(fail_search)

    ASSERT(is_search_context(bp));

    /* discard the current search space and context */
    discard_search_space();
    pop_search_context();

    /* return an empty list to the caller */
    TRACE(("leaving encapsulated search with no solution\n"));
    RETURN(nil);
}
