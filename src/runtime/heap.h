#line 26 "heap.nw"
/* booleans */
#ifndef __cplusplus
typedef enum bool { false, true } boolean;
#else
# define boolean bool
#endif /*__cplusplus*/

/* words */
#define word_size	sizeof(word)
#define wordsof(x)	((sizeof(x) + word_size - 1) / word_size)

typedef void *word;

#line 48 "heap.nw"
/* unboxed objects */
#if !ONLY_BOXED_OBJECTS
# define IF_UNBOXED(unboxed,boxed) unboxed
#else
# define IF_UNBOXED(unboxed,boxed) boxed
#endif

/* check for boxed-ness of a node */
#define is_unboxed(node)        IF_UNBOXED(((long)(node) & 0x01), 0)
#define is_boxed(node)          !is_unboxed(node)

#if !ONLY_BOXED_OBJECTS
# define mk_unboxed(x)		(Node *)(((x) << 1) | 0x01)
# define unboxed_val(node)	((long)(node) >> 1)
#endif

#line 77 "heap.nw"
/* tag values */
enum {
    ABSTRACT_TAG    = -13,	/* external objects */
    SCRIPT_TAG	    = -12,	/* saved script/trail */
    THREAD_TAG	    = -11,	/* threadqueue node */
    CHAR_TAG	    = -10,	/* character node */
    INT_TAG	    = -9,	/* integer number */
    FLOAT_TAG	    = -8,	/* floating-point number */
    PAPP_TAG	    = -7,	/* partial application node */
    CLOSURE_TAG     = -6,	/* closure node */
    SEARCH_CONT_TAG = -5,	/* search continuation */
    VARIABLE_TAG    = -4,	/* (unbound) logic variable */
    QUEUEME_TAG	    = -3,	/* locked suspended application node */
    SUSPEND_TAG	    = -2,	/* suspended application node */
    INDIR_TAG	    = -1	/* indirection node */
};

#line 126 "heap.nw"
/* node types -- defined below */
typedef union node	    Node;
typedef struct node_info    NodeInfo;
typedef union thread_node   *ThreadQueue;	/* defined in threads.h */
typedef struct search_space SearchSpace;	/* defined in spaces.h */
typedef struct constraint   Constraint;
typedef void (*FinalFun)(Node *);

struct node_info
{
    const int	       tag;		/* tag number */
    const unsigned int length;		/* length of the node */
    const int          *offset_table;	/* pointer offset table */
    const Label	       eval;		/* entrypoint for evaluation */
    const char	       *cname;		/* constructor name */
    const FinalFun     final_fun;	/* optional finalization function */
};

#define node_tag(node)		(node)->info->tag
#define node_size(node)		(node)->info->length
#define is_constr_node(node)	(node_tag(node) >= 0)
#define is_char_node(node)	(node_tag(node) == CHAR_TAG)
#define is_int_node(node) \
    IF_UNBOXED(is_unboxed(node), (node_tag(node) == INT_TAG))
#define is_float_node(node)	(node_tag(node) == FLOAT_TAG)
#define is_papp_node(node)	(node_tag(node) == PAPP_TAG)
#define is_closure_node(node)	(node_tag(node) == CLOSURE_TAG)
#define is_variable_node(node)	(node_tag(node) == VARIABLE_TAG)
#define is_suspend_node(node)	(node_tag(node) == SUSPEND_TAG)
#define is_queueMe_node(node)	(node_tag(node) == QUEUEME_TAG)
#define is_indir_node(node)	(node_tag(node) == INDIR_TAG)
#define is_search_cont_node(node) (node_tag(node) == SEARCH_CONT_TAG)
#define is_abstract_node(node)	(node_tag(node) <= ABSTRACT_TAG)

#define word_offsetof(type,field) \
    (int)((word *)&(((type *)0)->field) - (word *)0)

extern const int ot_binary[];

#line 176 "heap.nw"
struct constr_node {
    NodeInfo *info;
    Node     *args[1];
};

#define constr_argc(node)	(node_size(node) - 1)
#define constr_node_size(argc)	((argc) + 1)

#line 201 "heap.nw"
#define NIL_TAG  ___91__93__tag
#define CONS_TAG ___58__tag
#define UNIT_TAG ___40__41__tag
#define SUCCESS_TAG __Success_tag

#define nil_node_size	  constr_node_size(0)
#define cons_node_size	  constr_node_size(2)
#define unit_node_size	  constr_node_size(0)
#define success_node_size constr_node_size(0)

enum { NIL_TAG, CONS_TAG };
enum { UNIT_TAG };
enum { SUCCESS_TAG };

extern NodeInfo ___91__93__info, ___58__info;
extern NodeInfo ___40__41__info;
extern NodeInfo __Success_info;
extern NodeInfo *___91__93__node, *___40__41__node;
extern NodeInfo *__Success_node;

#define nil  (Node *)&___91__93__node
#define unit (Node *)&___40__41__node
#define Success (Node *)&__Success_node
#define cons_info ___58__info

extern boolean is_tuple(const NodeInfo *info);
extern boolean is_operator(const NodeInfo *info);

#line 294 "heap.nw"
struct vector_node {
    NodeInfo *info;
    unsigned length;
    Node     *args[1];
};

#define is_vector(node) ((node)->info->length == 0)
#define vector_argc(node) \
    (((struct vector_node *)(node))->length - vector_node_size(0))
#define vector_node_size(argc) \
    (wordsof(struct vector_node) + (argc) - 1)

#line 314 "heap.nw"
#define DECLARE_CONST(name) \
DECLARE_DATA(name); \
extern NodeInfo *name##_node

#define DECLARE_DATA(name) \
extern NodeInfo name##_info

#define DECLARE_VECTOR(name) \
DECLARE_DATA(name)

#define DEFINE_CONST(name,cname,tag) \
DEFINE_DATA(name,cname,tag,0); \
NodeInfo *name##_node = &name##_info

#define DEFINE_DATA(name,cname,tag,arity) \
NodeInfo name##_info = { \
    tag, constr_node_size(arity), (const int *)0, (Label)eval_whnf, cname, \
    (FinalFun)0 \
}

#define DEFINE_VECTOR(name,cname,tag) \
NodeInfo name##_info = { \
    tag, 0, (const int *)0, (Label)eval_whnf, cname, (FinalFun)0 \
}

#line 344 "heap.nw"
#if ONLY_BOXED_OBJECTS
extern NodeInfo int_info;
struct int_node {
    NodeInfo *info;
    long int i;
};
# define int_node_size		wordsof(struct int_node)
# define int_val(node)		(node)->i.i
#else
# define mk_int(i)		mk_unboxed(i)
# define int_node_size		0
# define int_val(node)		unboxed_val(node)
#endif

#line 383 "heap.nw"
extern NodeInfo float_info;
struct float_node {
    NodeInfo *info;
    double   d;
};
#define float_node_size         wordsof(struct float_node)

#if UNALIGNED_DOUBLE
# define get_float_val(_d,node)	_d = (node).d
# define put_float_val(node,_d)	(node).d = _d
#else
union _conv {
    double d;
    long   l[2];
};

# define get_float_val(_d,node) do { \
    union _conv conv; \
    conv.l[0] = ((long *)&(node).d)[0]; \
    conv.l[1] = ((long *)&(node).d)[1]; \
    _d = conv.d; \
} while ( 0 )
# define put_float_val(node,_d) do { \
    union _conv conv; \
    conv.d = _d; \
    ((long *)&(node).d)[0] = conv.l[0]; \
    ((long *)&(node).d)[1] = conv.l[1]; \
} while ( 0 )
#endif

#line 426 "heap.nw"
extern NodeInfo char_info;
struct char_node {
    NodeInfo *info;
    int ch;
};

#define char_node_size		wordsof(struct char_node)

extern struct char_node char_table[256];
extern void init_chars(void);

#line 465 "heap.nw"
typedef struct function_info {
    const NodeInfo     node_info;	/* common fields */
    const Label	       entry;		/* entry-point of the function */
    const unsigned int arity;		/* arity of the function */
} FunctionInfo;

struct closure_node {
    FunctionInfo *info;
    Node	 *args[1];		/* arguments */
};
#define closure_argc(node)      (node_size(node) - closure_node_size(0))
#define closure_node_size(argc) (wordsof(struct closure_node) + (argc-1))

#line 488 "heap.nw"
#define FUNINFO(fname,entrypoint,arity) \
{ { CLOSURE_TAG, closure_node_size(arity), (const int *)0, entrypoint##_eval, \
    fname, (FinalFun)0 }, entrypoint, arity }

#define PAPPINFO(fname,argc,entrypoint,arity) \
{ { PAPP_TAG, closure_node_size(argc), (const int *)0, eval_whnf, fname, \
    (FinalFun)0 }, entrypoint, arity },

#line 504 "heap.nw"
extern NodeInfo variable_info;
struct variable_node {
    NodeInfo	*info;
    Constraint	*cstrs;		/* constraint list */
    ThreadQueue	wq;		/* wait queue */
    SearchSpace	*spc;		/* defining search space */
};
#define variable_node_size      wordsof(struct variable_node)

#line 531 "heap.nw"
extern NodeInfo constraint_info;
struct constraint {
    NodeInfo   *info;
    Constraint *cstrs;		/* link to next constraint or 0 */
};

#line 545 "heap.nw"
struct suspend_node {
    NodeInfo	*info;
    Node	*fn;		/* pointer to function node */
    SearchSpace	*spc;		/* defining search space */
};
#define suspend_node_size       wordsof(struct suspend_node)

extern NodeInfo queueMe_info;
struct queueMe_node {
    NodeInfo	*info;
    ThreadQueue wq;		/* pointer to waitqueue */
    SearchSpace	*spc;		/* defining search space */
};
#define queueMe_node_size       wordsof(struct queueMe_node)

#line 574 "heap.nw"
#define SUSPINFO(entrypoint) { \
    SUSPEND_TAG, suspend_node_size, (const int *)0, entrypoint##_lazy, \
    (const char *)0, (FinalFun)0 \
}

#line 592 "heap.nw"
extern NodeInfo indir_info, suspend_indir_info, variable_indir_info;
struct indir_node {
    NodeInfo *info;
    Node     *node;
};
#define indir_node_size		wordsof(struct indir_node)

#line 618 "heap.nw"
extern NodeInfo search_cont_info;
struct search_cont_node {
    NodeInfo	*info;
    Label	code;		/* next instruction to be executed */
    Node	*susp;		/* suspended goal application */
    Node	*var;		/* goal variable */
    Node	*ds;		/* saved data stack */
    ThreadQueue rq;		/* saved ready queue */
    SearchSpace *spc;		/* local space of the continuation */
};
#define search_cont_node_size   wordsof(struct search_cont_node)

#line 641 "heap.nw"
union node {
    NodeInfo *info;
    struct char_node ch;
#if ONLY_BOXED_OBJECTS
    struct int_node i;
#endif
    struct float_node f;
    struct constr_node c;
    struct vector_node a;
    struct variable_node v;
    struct suspend_node s;
    struct queueMe_node q;
    struct indir_node n;
    struct closure_node cl;
    struct search_cont_node sc;
};

#line 669 "heap.nw"
extern word *hp, *hlim;
extern word *heap_base, *heap_end;

#line 693 "heap.nw"
extern boolean in_gc;
extern void collect(unsigned int);
#define CHECK_HEAP(n) do { if ( hp + (n) > heap_end ) collect(n); } while ( 0 )

#line 722 "heap.nw"
typedef struct global_root {
    struct global_root *next;
    Node	   **root;
} GlobalRoot;
extern GlobalRoot *global_roots;
extern Node	  **local_roots;

#line 746 "heap.nw"
#define LOCAL_ROOT_NODE __additional_roots__

#define DECLARE_LOCAL_ROOTS(n) \
    Node *LOCAL_ROOT_NODE[(n)+2]; \
    LOCAL_ROOT_NODE[0] = (Node *)n; \
    LOCAL_ROOT_NODE[1] = (Node *)local_roots; \
    local_roots = LOCAL_ROOT_NODE

#define ADD_LOCAL_ROOTS1(x) \
    DECLARE_LOCAL_ROOTS(1); \
    LOCAL_ROOT_NODE[2] = x
#define ADD_LOCAL_ROOTS2(x,y) \
    DECLARE_LOCAL_ROOTS(2); \
    LOCAL_ROOT_NODE[2] = x; \
    LOCAL_ROOT_NODE[3] = y
#define ADD_LOCAL_ROOTS3(x,y,z) \
    DECLARE_LOCAL_ROOTS(3); \
    LOCAL_ROOT_NODE[2] = x; \
    LOCAL_ROOT_NODE[3] = y; \
    LOCAL_ROOT_NODE[4] = z

#define DROP_LOCAL_ROOTS() local_roots = (Node **)LOCAL_ROOT_NODE[1]

#define LOCAL_ROOT (LOCAL_ROOT_NODE+2)

#line 780 "heap.nw"
extern void add_global_root(Node **root);
extern void remove_global_root(Node **root);

#line 830 "heap.nw"
extern void register_final(Node *node);

#line 840 "heap.nw"
extern void release_mem(void);

#line 849 "heap.nw"
extern void init_heap(unsigned long);

#line 856 "heap.nw"
extern void heap_exhausted(void) __attribute__ ((noreturn));

