#line 25 "threads.nw"
extern unsigned int cid;	/* id of current thread */
extern Node	**ds_base;

#line 80 "threads.nw"
#if 0
typedef union thread_node *ThreadQueue; /* already declared in heap.h */
#endif

#define THREAD_INFO \
    NodeInfo	     *info; \
    unsigned int     id;		/* (unique) thread id */ \
    ThreadQueue	     next;		/* link to next thread of queue */

struct thread_state {
    THREAD_INFO
    int		     reason;		/* reason for suspension */
    Label	     ip;		/* next instruction to be executed */
    ExceptionFrame   *efp;		/* pointer to exception frame */
    Node	     **ds_base;		/* base address of stack */
    unsigned int     ds_size;		/* size of data stack (segment) */
    Node	     *ds;		/* saved data stack */
};

struct thread_surrogate {
    THREAD_INFO
    ThreadQueue	     thd;		/* pointer to the "real" thread */
    ThreadQueue	     link;		/* ring of surrogates for the thread */
};

union thread_node {
    struct thread_state	    t;
    struct thread_surrogate s;
};

extern ThreadQueue rq;

#line 149 "threads.nw"
enum suspend_reason {
    None,			/* interrupted */
    Yield,			/* rescheduled due non-determinism */
    Delay,			/* suspended due to unbound variable */
    Eval			/* suspended due to locked application */
};

#line 183 "threads.nw"
extern void start_thread(unsigned int n);
DECLARE_ENTRYPOINT(stop_thread);
extern Label suspend_thread(Label l, Node *n);
extern Label delay_thread(Label l, Node *n);
extern Label yield_thread(Label l);
extern Label yield_delay_thread(Label l, Node *n);
extern Label activate_threads(ThreadQueue wq, Label l);
extern void wake_threads(ThreadQueue wq);
extern ThreadQueue join_queues(ThreadQueue tq1, ThreadQueue tq2);

#line 210 "threads.nw"
extern Node *save_continuation(Label l, Node **ds_base);
extern void restore_continuation(Node *cont);
extern Label resume_continuation(Node *cont);

