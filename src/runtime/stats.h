#line 21 "stats.nw"
extern void stats_init(int on);
extern void stats_terminate(unsigned long allocated);

extern void stats_begin_gc(unsigned long allocated);
extern void stats_end_gc(unsigned long allocated);

extern void stats_backtrack(unsigned long freed);

