#line 16 "print.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "trail.h"
#include "disequal.h"
#include "vars.h"
#include "char.h"
#include "print.h"

static void    print_node(unsigned, Node *);
static void    print_app(unsigned, Node *, unsigned, Node **);
static boolean is_string(Node *);
static void    print_string(Node *);
static void    print_list(Node *);
static void    print_tuple(Node *);
static boolean print_constraints(boolean, Node *);
static boolean print_app_constraints(boolean, unsigned, Node **);
static boolean print_constrained_var(boolean, Node *);

#line 53 "print.nw"
void
print_result(const char **var_names, Node **vars, Node *result)
{
    unsigned	     i, n;
    boolean	     hasAnswer;
    struct dict_node *tail;

    tail      = names_tail;
    hasAnswer = false;
    for ( n = 0; var_names[n] != (const char *)0; n++ )
    {
	if ( !is_variable_node(vars[n]) )
	{
	    if ( !hasAnswer )
	    {
		printf("{%s = ", var_names[n]);
		hasAnswer = true;
	    }
	    else
		printf(", %s = ", var_names[n]);
	    print_node(0, vars[n]);
	}
    }

    hasAnswer = print_constraints(hasAnswer, result);
    for ( i = 0; i < n; i++ )
	hasAnswer = print_constraints(hasAnswer, vars[i]);

    if ( hasAnswer )
	printf("} ");

    print_node(0, result);
    release_names(tail);
}

#line 101 "print.nw"
static void
print_node(unsigned prec, Node *node)
{
    char	 buf[32], *cp;
    unsigned int i;
    double	 d;

    for (;;)
    {
#if !ONLY_BOXED_OBJECTS
	if ( is_unboxed(node) )
	{
	    printf(prec > 0 && unboxed_val(node) < 0 ? "(%ld)" : "%ld",
		   unboxed_val(node));
	    return;
	}
	else
#endif
	    switch ( node_tag(node) )
	    {
	    case CHAR_TAG:
		printf("'%s'", lit_char(node->ch.ch, '\''));
		return;

#if ONLY_BOXED_OBJECTS
	    case INT_TAG:
		printf(prec > 0 && node->i.i < 0 ? "(%ld)" : "%ld",
		       node->i.i);
		return;
#endif
	    case FLOAT_TAG:
		get_float_val(d, node->f);
		sprintf(buf, "%g", d);

		cp = strpbrk(buf, ".e");
		if ( cp == (char *)0 )
		    strcat(buf, ".0");
		else if ( *cp != '.'  )
		{
		    i = strlen(cp) + 1;
		    for ( cp += i; i-- > 0; cp-- )
			cp[2] = cp[0];
		    cp[1] = '.';
		    cp[2] = '0';
		}
		printf(prec > 0 && buf[0] == '-' ? "(%s)" : "%s", buf);
		return;
	    case PAPP_TAG:
	    case CLOSURE_TAG:
		print_app(prec, node, closure_argc(node), node->cl.args);
		return;
	    case VARIABLE_TAG:
		printf("%s", lookup_name(node));
		return;
	    case SUSPEND_TAG:
		node = node->s.fn;
		break;
	    case QUEUEME_TAG:
		printf("Suspended");
		return;
	    case INDIR_TAG:
		node = node->n.node;
		break;
	    default:
		if ( is_abstract_node(node) || is_search_cont_node(node) )
		{
		    const char *name = node->info->cname;
		    if ( name == (const char *)0 )
			name = "<abstract>";
		    printf("%s", name);
		}
		else if ( node->info == (NodeInfo *)&cons_info )
		{
		    if ( is_string(node) )
			print_string(node);
		    else
			print_list(node);
		}
		else if ( is_tuple(node->info) )
		    print_tuple(node);
		else if ( is_vector(node) )
		    print_app(prec, node, vector_argc(node), node->a.args);
		else
		    print_app(prec, node, constr_argc(node), node->c.args);
		return;
	    }
    }
}

static void
print_app(unsigned prec, Node *node, unsigned argc, Node **argv)
{
    unsigned i;
    boolean  isop   = is_operator(node->info);
    boolean  infix  = isop && argc == 2;
    boolean  parens = infix ? prec > 0 : prec > 1 && argc != 0;

    if ( parens )
	putchar('(');

    if ( infix )
    {
	print_node(1, argv[0]);
	printf(" %s ", node->info->cname);
	print_node(1, argv[1]);
    }
    else
    {
	printf(isop ? "(%s)" : "%s", node->info->cname);

	for ( i = 0; i < argc ; i++ )
	{
	    putchar(' ');
	    print_node(2, argv[i]);
	}
    }

    if ( parens )
	putchar(')');
}

#line 234 "print.nw"
static boolean
is_string(Node *list)
{
    Node *head;

    while ( list->info == &cons_info )
    {
	head = list->c.args[0];
	while ( is_boxed(head) && head->info->tag == INDIR_TAG )
	    head = head->n.node;
	if ( is_unboxed(head) || head->info->tag != CHAR_TAG )
	    return false;

	list = list->c.args[1];
	while ( list->info->tag == INDIR_TAG )
	    list = list->n.node;
    }
    
    return list == nil;
}

static void
print_string(Node *list)
{
    Node *head;

    putchar('"');
    while ( list->info == &cons_info )
    {
	head = list->c.args[0];
	while ( is_boxed(head) && head->info->tag == INDIR_TAG )
	    head = head->n.node;
	ASSERT(is_boxed(head) && head->info->tag == CHAR_TAG);
	printf("%s", lit_char(head->ch.ch, '"'));

	list = list->c.args[1];
	while ( list->info->tag == INDIR_TAG )
	    list = list->n.node;
   }
   ASSERT(list == nil);
   putchar('"');
}

static void
print_list(Node *list)
{
    char sep = '[';

    while ( list->info == &cons_info )
    {
	putchar(sep);
	print_node(0, list->c.args[0]);
	sep = ',';

	list = list->c.args[1];
	while ( list->info->tag == INDIR_TAG )
	    list = list->n.node;
    }

    if ( list != nil )
    {
	putchar('|');
	print_node(0, list);
    }

    putchar(']');
}

static void
print_tuple(Node *node)
{
    unsigned int i, n;
    boolean	 first = true;
    Node	 **argv;

    putchar('(');

    if ( is_vector(node) )
    {
	n    = vector_argc(node);
	argv = node->a.args;
    }
    else
    {
	n    = constr_argc(node);
	argv = node->c.args;
    }
    for ( i = 0; i < n; i++ )
    {
	if ( first )
	    first = false;
	else
	    printf(",");
	print_node(0, argv[i]);
    }

    putchar(')');
}

#line 342 "print.nw"
static boolean
print_constraints(boolean hasAnswer, Node *node)
{
    for (;;)
    {
	if ( is_boxed(node) )
	    switch ( node_tag(node) )
	    {
	    case PAPP_TAG:
	    case CLOSURE_TAG:
		hasAnswer = print_app_constraints(hasAnswer,
						  closure_argc(node),
						  node->cl.args);
		break;
	    case VARIABLE_TAG:
		if ( node->v.cstrs != (Constraint *)0 )
		    hasAnswer = print_constrained_var(hasAnswer, node);
		break;
	    case SUSPEND_TAG:
		node = node->s.fn;
		continue;
	    case INDIR_TAG:
		node = node->n.node;
		continue;
	    default:
		if ( is_constr_node(node) )
		{
		    if ( is_vector(node) )
			hasAnswer = print_app_constraints(hasAnswer,
							  vector_argc(node),
							  node->a.args);
		    else
			hasAnswer = print_app_constraints(hasAnswer,
							  constr_argc(node),
							  node->c.args);
		}
		break;
	    }
	break;
    }
    return hasAnswer;
}

static boolean
print_app_constraints(boolean hasAnswer, unsigned argc, Node **argv)
{
    unsigned i;

    for ( i = 0; i < argc; i++ )
	hasAnswer = print_constraints(hasAnswer, argv[i]);

    return hasAnswer;
}

static boolean
print_constrained_var(boolean hasAnswer, Node *var)
{
    Constraint *cstrs;

    ASSERT(is_variable_node(var) && var->v.cstrs != (Constraint *)0);

    cstrs = var->v.cstrs;
    SAVE(var, v.cstrs);
    var->v.cstrs = (Constraint *)0;

    for ( ; cstrs != (Constraint *)0; cstrs = cstrs->cstrs )
    {
	if ( !hasAnswer )
	{
	    printf("{");
	    hasAnswer = true;
	}
	else
	    printf(", ");
	print_node(0, var);
	printf(" /= ");
	print_node(0, ((Disequality *)cstrs)->node);

	hasAnswer = print_constraints(hasAnswer, ((Disequality *)cstrs)->node);
    }

    return hasAnswer;
}
