#line 38 "trace.nw"
#define TRACE(x) do { if ( do_trace ) trace x; } while ( 0 )

extern int do_trace;
void trace(const char *fmt, ...);

