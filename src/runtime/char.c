#line 24 "char.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "eval.h"
#include "threads.h"
#include "cam.h"
#include "trace.h"
#include "char.h"

static const char *asciiTab[] = {
    "\\NUL", "\\SOH", "\\STX", "\\ETX", "\\EOT", "\\ENQ", "\\ACK", "\\a",
    "\\b",   "\\t",   "\\n",   "\\v",   "\\f",   "\\r",  "\\SO",  "\\SI",
    "\\DLE", "\\DC1", "\\DC2", "\\DC3", "\\DC4", "\\NAK", "\\SYN", "\\ETB",
    "\\CAN", "\\EM",  "\\SUB", "\\ESC", "\\FS",  "\\GS",  "\\RS",  "\\US"
};

const char *
lit_char(int c, char q)
{
    static char buf[8], *cp;
    
    if ( c >= '\0' && c < ' ' )
	return asciiTab[c];
    else if ( c == 0177 )
	return "\\DEL";

    if ( c >= ' ' && c < 0177 )
    {
	cp = buf;
	if ( c == q || c == '\\' )
	    *cp++ = '\\';
	*cp++ = c;
	*cp   = '\0';
    }
    else
	sprintf(buf, "\\%d", c);

    return (const char *)buf;
}

#line 76 "char.nw"
DECLARE_ENTRYPOINT(__ord);

FUNCTION(__ord)
{
    int c;
    Node *r;

    EXPORT_LABEL(__ord)
 ENTRY_LABEL(__ord)
    EVAL_RIGID_CHAR(__ord);
    c	= (*sp++)->ch.ch;

#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = c;
    hp	   += int_node_size;
#else
    r = mk_int(c);
#endif

    RETURN(r);
}


DECLARE_ENTRYPOINT(__chr);

FUNCTION(__chr)
{
    int c;

    EXPORT_LABEL(__chr)
 ENTRY_LABEL(__chr)
    EVAL_RIGID_INT(__chr);
    c	= int_val(sp[0]);
    sp += 1;

    if ( c < 0 || c > 255 )
    {
	fprintf(stderr, "chr: code %d is out-of-range\n", c);
	exit(1);
    }
   RETURN((Node *)(char_table + c));
}
