#line 45 "trace.nw"
#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "eval.h"
#include "char.h"
#include "trace.h"

#if 0
/* This variable must be defined by the main program */
int do_trace;
#endif

static void trace_showaddr(Node *node);
static void trace_shownode(int depth, Node *node);
static void trace_showapp(int depth, Node *node, unsigned argc, Node **argv);

void
trace(const char *fmt, ...)
{
    va_list	 ap;
    const char	 *cp;
    Node	 **fp, **argv;
    int		 depth = do_trace - 1;
    unsigned int i, argc;
    extern char	 **environ;

    va_start(ap, fmt);
    for ( cp = fmt; *cp != '\0'; cp++ )
    {
	if ( *cp == '%' )
	    switch ( *++cp )
	    {
	    case 'c':
		fprintf(stderr, "%c", va_arg(ap, int));
	        break;
	    case 'd':
	        fprintf(stderr, "%d", va_arg(ap, int));
	        break;
	    case 'g':
	        fprintf(stderr, "%g", va_arg(ap, double));
	        break;
	    case 's':
		fprintf(stderr, "%s", va_arg(ap, const char *));
		break;
	    case 'u':
		fprintf(stderr, "%u", va_arg(ap, unsigned int));
		break;
	    case 'x':
		fprintf(stderr, "%x", va_arg(ap, unsigned int));
		break;
	    case 'A':
		trace_showaddr(va_arg(ap, Node *));
		break;
	    case 'I':
		fprintf(stderr, "[%u]", cid);
		for ( fp = sp; fp < ds_base; fp++ )
		    if ( *fp != (Node *)0 && is_boxed(*fp)
			 && (char *)*fp < (char *)&environ
			 && (Label)*fp != update )
			fputc(' ', stderr);
		break;
	    case 'N':
	        trace_shownode(depth, va_arg(ap, Node *));
		break;
	    case 'V':
	    	argc = va_arg(ap, unsigned int);
	        argv = va_arg(ap, Node **);
	        for ( i = 0; i < argc; i++ )
		{
		    fputc(' ', stderr);
	    	    trace_shownode(depth, argv[i]);
		}
		break;
	    default:
		fputc(*cp, stderr);
		break;
	    }
	else
	    fputc(*cp, stderr);
    }
    va_end(ap);
}

static void
trace_showaddr(Node *node)
{
    if ( node == (Node *)0 )
	fprintf(stderr, "-null-");
#if !ONLY_BOXED_OBJECTS
    else if ( is_unboxed(node) )
	fprintf(stderr, "-unboxed%ld-", unboxed_val(node));
#endif
    else if ( heap_base <= (word *)node && (word *)node <= heap_end )
	fprintf(stderr, "-node%u-", node - (Node *)heap_base);
    else
	fprintf(stderr, "%p", node);
}

static void
trace_shownode(int depth, Node *node)
{
    double d;

    if ( node == (Node *)0 )
	fprintf(stderr, "-null-");
#if !ONLY_BOXED_OBJECTS
    else if ( is_unboxed(node) )
	fprintf(stderr, "%ld", unboxed_val(node));
#endif
    else
	switch ( node_tag(node) )
	{
	case CHAR_TAG:
	    fprintf(stderr, "'%s'", lit_char(node->ch.ch, '\''));
	    break;
#if ONLY_BOXED_OBJECTS
	case INT_TAG:
	    fprintf(stderr, "%ld", node->i.i);
	    break;
#endif
	case FLOAT_TAG:
	    get_float_val(d, node->f);
	    fprintf(stderr, "%g", d);
	    break;
	case VARIABLE_TAG:
	    fprintf(stderr, "var@%p", node);
	    break;
	case QUEUEME_TAG:
	    fprintf(stderr, "que@%p", node);
	    break;
	case SUSPEND_TAG:
	    fprintf(stderr, "susp@%p=", node);
	    trace_shownode(depth, node->s.fn);
	    break;
	case PAPP_TAG:
	case CLOSURE_TAG:
	    trace_showapp(depth, node, closure_argc(node), node->cl.args);
	    break;
	case SEARCH_CONT_TAG:
	    fprintf(stderr, "cont@%p", node);
	    break;
	case INDIR_TAG:
	    trace_shownode(depth, node->n.node);
	    break;
	default:
	    if ( is_abstract_node(node) )
	    {
		const char *name = node->c.info->cname;
		if ( name == (const char *)0 )
		    name = "<abstract>";
		fprintf(stderr, "%s@%p", name, node);
	    }
	    else if ( is_vector(node) )
		trace_showapp(depth, node, vector_argc(node), node->a.args);
	    else
		trace_showapp(depth, node, constr_argc(node), node->c.args);
	    break;
	}
}

static void
trace_showapp(int depth, Node *node, unsigned argc, Node **argv)
{
    unsigned i;

    if ( argc > 0 )
	fputc('(', stderr);

    fprintf(stderr, "%s", node->c.info->cname);
    if ( depth > 0 )
	for ( i = 0; i < argc; i++ )
	{
	    fputc(' ', stderr);
	    trace_shownode(depth - 1, argv[i]);
	}
    else if ( argc > 0 )
	fprintf(stderr, " ...");

    if ( argc > 0 )
	fputc(')', stderr);
}
