#line 21 "stack.nw"
extern Node **stack_base, **stack_end;
extern Node **sp;

#line 43 "stack.nw"
extern void init_stack(unsigned int stack_size);

#line 71 "stack.nw"
extern void stack_overflow(void) __attribute__ ((noreturn));

#define CHECK_STACK1()	 if ( sp == stack_base ) stack_overflow();
#define CHECK_STACK(n)	 if ( sp - (n) < stack_base ) stack_overflow();

#line 101 "stack.nw"
typedef struct choicepoint {
    Label	       *btAlts;		/* remaining alternatives */
    unsigned int       btCid;		/* id of current thread */
    Node	       **btDsBase;	/* saved thread stack base */
    struct choicepoint *btBp;		/* previous choicepoint */
    union thread_node  *btRq;		/* saved run queue */
    struct save_rec    *btTp;		/* saved trail pointer */
    struct dict_node   *btDict;		/* saved dictionary tail pointer */
    word	       *btHp;		/* saved heap pointer */
} Choicepoint;

extern Choicepoint *bp;

#line 127 "stack.nw"
#define is_search_context(cp)	((cp)->btAlts == (Label *)0)

#line 147 "stack.nw"
extern Label *choice_conts;

extern struct nondet_handlers {
    Label choices;
    Label deadlock;
    Label fail;
} nondet_handlers;

#line 180 "stack.nw"
typedef struct exception_frame
{
    Node		   *handler;
    struct exception_frame *frame;
} ExceptionFrame;

extern ExceptionFrame *efp;

