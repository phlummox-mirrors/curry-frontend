#line 11 "unify.nw"
extern Label bind_var(Node *, Node *, Label);

DECLARE_ENTRYPOINT(___61__58__61_);

#if NO_OCCURS_CHECK
# define occurs(var,arg)	false
#else
extern boolean occurs(Node *, Node *);
#endif

