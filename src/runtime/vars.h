#line 37 "vars.nw"
struct dict_node {
    Node	     *node;		/* variable node         */
    const char	     *name;		/* name of variables     */
    struct dict_node *next;		/* link to next variable */
};

extern struct dict_node *names_dict, *names_tail;

#line 58 "vars.nw"
extern void add_name(Node *node, const char *name);

#line 100 "vars.nw"
extern void release_names(struct dict_node *new_tail);

#line 155 "vars.nw"
extern void cleanup_names(void);

#line 209 "vars.nw"
extern const char *lookup_name(Node *node);

