#line 33 "main.nw"
#define k 1024
#define M k*k

#ifndef DEFAULT_HEAPSIZE
# define DEFAULT_HEAPSIZE 4*M
#endif

#ifndef DEFAULT_STACKSIZE
# define DEFAULT_STACKSIZE 512*k
#endif
#ifndef DEFAULT_TRAILSIZE
# define DEFAULT_TRAILSIZE 512*k
#endif

#ifndef DEFAULT_SHOW_STATS
# define DEFAULT_SHOW_STATS 0
#endif

#ifndef DEFAULT_DO_TRACE
# define DEFAULT_DO_TRACE 0
#endif

extern unsigned int heapsize;
extern unsigned int stacksize;
extern unsigned int trailsize;

extern int do_trace;
extern int show_stats;

extern unsigned int pagesize;
extern unsigned int pagemask;

extern void curry_init(int *argc, char *argv[]);
extern void curry_terminate(void);

