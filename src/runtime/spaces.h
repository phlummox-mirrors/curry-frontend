#line 18 "spaces.nw"
#if 0
typedef struct search_space SearchSpace; /* already declared in heap.h */
#endif
typedef struct script Script;

struct search_space {
    NodeInfo	*info;
    SearchSpace	*root;		/* pointer to root space */
    SearchSpace	*parent;	/* parent space */
    SearchSpace	*active;	/* active space (valid only on root) */
    Script	*script;	/* saved local bindings */
};

extern struct search_space *ss;

#line 67 "spaces.nw"
#define is_local_space(space) ( \
    ss == (SearchSpace *)0 \
    ? (space) == (SearchSpace *)0 \
    : (space) != (SearchSpace *)0 && (space)->root == ss->root \
)

#line 81 "spaces.nw"
typedef struct script_rec {
    word	 *addr;		/* address to be updated */
    word	 inInfo;	/* info vector inside space */
    word	 outInfo;	/* info vector outside space */
    unsigned int ofs;		/* offset within node */
    word	 inVal;		/* value inside space */
    word	 outVal;	/* value outside space */
} ScriptRec;

struct script {
    NodeInfo  *info;
    unsigned  length;
    ScriptRec data[1];
};

#line 252 "spaces.nw"
extern void new_search_space(SearchSpace *);

#line 290 "spaces.nw"
extern boolean inject_search_space(SearchSpace *);

#line 314 "spaces.nw"
extern void save_search_space(void);

#line 363 "spaces.nw"
extern void discard_search_space(void);

#line 382 "spaces.nw"
extern void resume_search_space(SearchSpace *space);

#line 427 "spaces.nw"
extern Node *copy_graph(Node *graph, SearchSpace *space);

