#line 20 "cam.nw"
#define RETURN(_res) { \
    Label ret_ip = (Label)sp[0]; \
    sp[0] = (_res); \
    TRACE(("%I return %N\n", (_res))); \
    GOTO(ret_ip); \
}

#define ENTER(_node) { \
    if ( is_boxed(_node) ) { \
	CHECK_STACK1(); \
	*--sp = (_node); \
	GOTO((_node)->info->eval); \
    } \
    RETURN(_node); \
}

#line 40 "cam.nw"
#define FAIL() GOTO(nondet_handlers.fail)

#line 55 "cam.nw"
#define EVAL_RIGID(l) \
for (;;) { \
    switch ( sp[0]->info->tag ) { \
    case INDIR_TAG: sp[0] = sp[0]->n.node; continue; \
    case CLOSURE_TAG: case SUSPEND_TAG: case QUEUEME_TAG: \
	CHECK_STACK1(); sp -= 1; sp[0] = sp[1]; sp[1] = (Node *)(l); \
	GOTO(sp[0]->info->eval); \
    case VARIABLE_TAG: GOTO(delay_thread(l, sp[0])); \
    default: break; \
    } \
    break; \
}

#define EVAL_RIGID_CHAR(l) \
for (;;) { \
    switch ( sp[0]->info->tag ) { \
    case INDIR_TAG: sp[0] = sp[0]->n.node; continue; \
    case CLOSURE_TAG: case SUSPEND_TAG: case QUEUEME_TAG: \
	CHECK_STACK1(); sp -= 1; sp[0] = sp[1]; sp[1] = (Node *)(l); \
	GOTO(sp[0]->info->eval); \
    case VARIABLE_TAG: GOTO(delay_thread(l, sp[0])); \
    default: ASSERT(sp[0]->info->tag == CHAR_TAG); break; \
    } \
    break; \
}

#define EVAL_RIGID_INT(l) \
for (;;) { \
    if ( is_boxed(sp[0]) ) \
	switch ( sp[0]->info->tag ) { \
	case INDIR_TAG: sp[0] = sp[0]->n.node; continue; \
	case CLOSURE_TAG: case SUSPEND_TAG: case QUEUEME_TAG: \
	    CHECK_STACK1(); sp -= 1; sp[0] = sp[1]; sp[1] = (Node *)(l); \
	    GOTO(sp[0]->info->eval); \
	case VARIABLE_TAG: GOTO(delay_thread(l, sp[0])); \
	default: ASSERT(sp[0]->info->tag == INT_TAG); break; \
	} \
    break; \
}

#define EVAL_RIGID_FLOAT(l) \
for (;;) { \
    switch ( sp[0]->info->tag ) { \
    case INDIR_TAG: sp[0] = sp[0]->n.node; continue; \
    case CLOSURE_TAG: case SUSPEND_TAG: case QUEUEME_TAG: \
	CHECK_STACK1(); sp -= 1; sp[0] = sp[1]; sp[1] = (Node *)(l); \
	GOTO(sp[0]->info->eval); \
    case VARIABLE_TAG: GOTO(delay_thread(l, sp[0])); \
    default: ASSERT(sp[0]->info->tag == FLOAT_TAG); break; \
    } \
    break; \
}

#define EVAL_FLEX_POLY(l) \
for (;;) { \
    if ( is_boxed(sp[0]) ) \
	switch ( sp[0]->info->tag ) { \
	case INDIR_TAG: sp[0] = sp[0]->n.node; continue; \
	case CLOSURE_TAG: case SUSPEND_TAG: case QUEUEME_TAG: \
	    CHECK_STACK1(); sp -= 1; sp[0] = sp[1]; sp[1] = (Node *)(l); \
	    GOTO(sp[0]->info->eval); \
	default: break; \
	} \
    break; \
}

#define EVAL_RIGID_POLY(l) \
for (;;) { \
    if ( is_boxed(sp[0]) ) \
	switch ( sp[0]->info->tag ) { \
	case INDIR_TAG: sp[0] = sp[0]->n.node; continue; \
	case CLOSURE_TAG: case SUSPEND_TAG: case QUEUEME_TAG: \
	    CHECK_STACK1(); sp -= 1; sp[0] = sp[1]; sp[1] = (Node *)(l); \
	    GOTO(sp[0]->info->eval); \
	case VARIABLE_TAG: GOTO(delay_thread(l, sp[0])); \
	default: break; \
	} \
    break; \
}
