#line 47 "trail.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include "run.h"
#include "heap.h"
#include "trail.h"
#include "main.h"

SaveRec *tp;
SaveRec *trail_base;
SaveRec *trail_end;

void
trail_overflow()
{
    fprintf(stderr, "Trail overflow, aborting ...\n");
    exit(2);
}

#line 75 "trail.nw"
void
init_trail(unsigned int trail_size)
{
    trail_size = (trail_size + pagemask) & ~pagemask;
    trail_base = (SaveRec *)malloc(trail_size + pagemask);
    if ( trail_base == (SaveRec *)0 )
    {
	fprintf(stderr, "not enough memory to allocate trail\n");
	exit(1);
    }

    trail_base = (SaveRec *)(((long)trail_base + pagemask) & ~pagemask);
    trail_end = trail_base + trail_size / sizeof(SaveRec);
    tp	      = trail_base;
}

