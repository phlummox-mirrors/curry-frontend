#line 36 "stats.nw"
#include "config.h"
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include "stats.h"

#line 219 "stats.nw"
static void add_timeval(struct timeval *, struct timeval);
static void sub_timeval(struct timeval *, struct timeval);

#line 53 "stats.nw"
static int show_stats;

#line 65 "stats.nw"
static struct timeval user_time, gc_time, sys_time, real_time;

#line 74 "stats.nw"
unsigned long      n_gc;
unsigned long long total_collect, total_release, total_live;

#line 164 "stats.nw"
static unsigned long n_alloc_before_gc;


#line 86 "stats.nw"
void
stats_init(int level)
{
    struct rusage  ru;
    struct timeval tv;
    show_stats = level;

    gettimeofday(&tv, (struct timezone *)0);
    getrusage(RUSAGE_SELF, &ru);
    sub_timeval(&user_time, ru.ru_utime);
    sub_timeval(&sys_time, ru.ru_stime);
    sub_timeval(&real_time, tv);
}

#line 108 "stats.nw"
void
stats_terminate(unsigned long allocated)
{
    struct rusage      ru;
    struct timeval     tv;
    unsigned long long total_alloc;

    gettimeofday(&tv, (struct timezone *)0);
    getrusage(RUSAGE_SELF, &ru);
    add_timeval(&user_time, ru.ru_utime);
    add_timeval(&sys_time, ru.ru_stime);
    add_timeval(&real_time, tv);

    total_alloc = allocated + total_collect + total_release;

    if ( show_stats > 0 )
    {
        fprintf(stderr,
		"[user: %lu.%03us, gc: %lu.%03us,"
		" sys: %lu.%03us, real: %lu.%03us]\n",
                (unsigned long)user_time.tv_sec,
		(unsigned)user_time.tv_usec / 1000,
                (unsigned long)gc_time.tv_sec,
		(unsigned)gc_time.tv_usec / 1000,
                (unsigned long)sys_time.tv_sec,
		(unsigned)sys_time.tv_usec / 1000,
                (unsigned long)real_time.tv_sec,
		(unsigned)real_time.tv_usec / 1000);

        fprintf(stderr, "[%llu words allocated", total_alloc);
        if ( n_gc > 0 )
	    fprintf(stderr,
		    ", %lu collection%s copying %llu words (%.2g%% live)",
		    n_gc, n_gc > 1 ? "s" : "", total_live,
		    (double)total_live / (total_live + total_collect) * 100);
	fprintf(stderr, "]\n");
    }
}

#line 168 "stats.nw"
void
stats_begin_gc(unsigned long n_alloc)
{
    struct rusage ru;

    getrusage(RUSAGE_SELF, &ru);
    add_timeval(&user_time, ru.ru_utime);
    sub_timeval(&gc_time, ru.ru_utime);

    n_alloc_before_gc = n_alloc;
    if ( show_stats > 1 )
        fprintf(stderr, "<GC: ");
}

void
stats_end_gc(unsigned long n_alloc)
{
    struct rusage ru;

    n_gc++;
    total_collect += n_alloc_before_gc - n_alloc;
    total_live	  += n_alloc;

    getrusage(RUSAGE_SELF, &ru);
    add_timeval(&gc_time, ru.ru_utime);
    sub_timeval(&user_time, ru.ru_utime);

    if ( show_stats > 1 )
        fprintf(stderr, "%lu live words, %lu words freed>\n",
                n_alloc, n_alloc_before_gc - n_alloc);
}

#line 205 "stats.nw"
void
stats_backtrack(unsigned long n_freed)
{
    total_release += n_freed;
}

#line 224 "stats.nw"
static void
add_timeval(struct timeval *p_tv1, struct timeval tv2)
{
    p_tv1->tv_sec += tv2.tv_sec;
    p_tv1->tv_usec += tv2.tv_usec;
    if ( p_tv1->tv_usec >= 1000000 )
    {
        p_tv1->tv_sec++;
        p_tv1->tv_usec -= 1000000;
    }
}

static void
sub_timeval(struct timeval *p_tv1, struct timeval tv2)
{
    p_tv1->tv_sec -= tv2.tv_sec;
    if ( p_tv1->tv_usec >= tv2.tv_usec )
        p_tv1->tv_usec -= tv2.tv_usec;
    else
    {
        p_tv1->tv_sec--;
        p_tv1->tv_usec += 1000000 - tv2.tv_usec;
    }
}
