#line 13 "cstring.nw"
extern Node	*from_string(const char *cp);
extern Node	*prefix_string(const char *cp, Node *);
extern unsigned string_length(Node *);
extern char	*copy_string(Node *, char *buf);
extern char	*to_string(Node *);

DECLARE_ENTRYPOINT(nf_string);

