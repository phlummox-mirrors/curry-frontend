#line 19 "io_monad.nw"
extern int  curry_exec(FunctionInfo *main_info_table, int argc, char **argv);
extern void curry_exit(int rc) __attribute__((noreturn));

extern Node *getProgName(void);
extern Node *getArgs(void);

DECLARE_ENTRYPOINT(__ioError);

