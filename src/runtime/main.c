#line 82 "main.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "trail.h"
#include "files.h"
#include "trace.h"
#include "main.h"
#include "stats.h"

static void	    bad_option(void) __attribute__((noreturn));
static unsigned int parse_size(const char *, const char *);

#define DEFAULT_PAGESIZE 4*k

unsigned int pagesize, pagemask;

static void
bad_option()
{
    fprintf(stderr, "Valid runtime system options:\n");
    fprintf(stderr, " -b MODE  set buffer mode for standard input/output\n");
    fprintf(stderr, "          valid MODEs: n  unbuffered\n");
    fprintf(stderr, "                       l  line buffered\n");
    fprintf(stderr, "                       f  fully buffered\n");
    fprintf(stderr, " -d       trace program execution\n");
    fprintf(stderr, " -h SIZE  set heap size to SIZE bytes (default: %d)\n",
	    heapsize);
    fprintf(stderr, " -p       print statistics at end of run\n");
    fprintf(stderr, " -k SIZE  set stack size to SIZE bytes (default: %d)\n",
	    stacksize);
    fprintf(stderr, " -t SIZE  set trail size to SIZE bytes (default: %d)\n",
	    trailsize);
    exit(1);
}

void
curry_init(int *p_argc, char *argv[])
{
    boolean rts;
    char    *cp, *arg;
    int	    i, j, argc;
    int     bufmode = -1, bufsize = 0;

    /* get system page size */
    pagesize = getpagesize();
    if ( pagesize == (unsigned)-1 )
	pagesize = DEFAULT_PAGESIZE;
    pagemask = pagesize - 1;

    /* process rts options */
    argc = *p_argc;
    rts	 = false;
    for ( i = j = 1; i < argc; i++ )
    {
	cp = argv[i];
	if ( !rts )
	    if ( strcmp(cp, "+RTS") == 0 )
		rts = true;
	    else
		argv[j++] = cp;
	else if ( strcmp(cp, "-RTS") == 0 )
	    rts = false;
	else
	{
	    if ( *cp == '-' )
		for ( cp++; *cp != '\0'; cp++ )
		    switch ( *cp )
		    {
		    case 'd':
			do_trace++;
			break;
		    case 'p':
			show_stats++;
			break;
		    case 'b':
		    case 'h':
		    case 'k':
		    case 't':
			if ( cp[1] != '\0' )
			    arg = cp + 1;
			else if ( ++i < argc )
			    arg = argv[i];
			else
			{
			    fprintf(stderr, "%s: missing argument after -%c\n",
				    argv[0], *cp);
			    bad_option();
			}
			switch ( *cp )
			{
			case 'b':
			    if ( strcmp(arg, "n") == 0 )
				bufmode = _IONBF;
			    else if ( strcmp(arg, "l") == 0 )
				bufmode = _IOLBF;
			    else if ( strcmp(arg, "f") == 0 )
				bufmode = _IOFBF;
			    else if ( *arg == 'f' )
			    {
				bufmode = _IOFBF;
				bufsize = parse_size("buffer size", arg + 1);
			    }
			    else
			    {
				fprintf(stderr,
					"%s: invalid file buffer mode %s\n",
					argv[0], arg);
				bad_option();
			    }
			    break;
			case 'h':
			    heapsize = parse_size("heap size", arg);
			    break;
			case 'k':
			    stacksize = parse_size("stack size", arg);
			    break;
			case 't':
			    trailsize = parse_size("trail size", arg);
			    break;
			}
			cp = "\0";
			break;
		    default:
			fprintf(stderr,
				"%s: unknown runtime system option %c\n",
				argv[0], *cp);
			bad_option();
		    }
	    else
	    {
		fprintf(stderr, "%s: unknown runtime system argument %s\n",
			argv[0], cp);
		bad_option();
	    }
	}
    }
    argv[j] = (char *)0;
    *p_argc = j;

    /* initialize runtime system */
    init_chars();
    init_stack(stacksize);
    init_trail(trailsize);
    init_heap(heapsize);
    init_files(bufmode, bufsize);
    stats_init(show_stats);
}

void
curry_terminate()
{
    stats_terminate(hp - heap_base);
}

#line 248 "main.nw"
static unsigned int
parse_size(const char *what, const char *arg)
{
    long size;
    char *end;

    size = strtol(arg, &end, 0);
    if ( *end != '\0' )
    {
	if ( strcmp(end, "m") == 0 || strcmp(end, "M") == 0 )
	{
	    size = size > LONG_MAX / M ? LONG_MAX : size * M;
	}
	else if ( strcmp(end, "k") == 0 || strcmp(end, "K") == 0 )
	{
	    size = size > LONG_MAX / k ? LONG_MAX : size * k;
	}
	else
	    size = -1;
    }

    if ( size <= 0 )
    {
	fprintf(stderr, "invalid %s: %s\n", what, arg);
	exit(1);
    }

    return size > LONG_MAX ? LONG_MAX : size;
}
