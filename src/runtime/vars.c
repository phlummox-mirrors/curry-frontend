#line 14 "vars.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "vars.h"

#line 47 "vars.nw"
struct dict_node *names_dict;
struct dict_node *names_tail;

#line 62 "vars.nw"
void
add_name(Node *node, const char *name)
{
    struct dict_node *next;

    next = (struct dict_node *)malloc(sizeof(struct dict_node));
    if ( next == (struct dict_node *)0 )
    {
	fprintf(stderr, "dictionary space exhausted, aborting ...\n");
	exit(2);
    }
    next->node = node;
    next->name = name;
    next->next = (struct dict_node *)0;

    if ( names_tail == (struct dict_node *)0 )
    {
	ASSERT(names_dict == (struct dict_node *)0);
	names_dict = names_tail = next;
    }
    else
    {
	names_tail->next = next;
	names_tail	 = next;
    }
}

#line 104 "vars.nw"
void
release_names(struct dict_node *new_tail)
{
    struct dict_node *curr, *next;

    if ( new_tail != names_tail )
    {
	names_tail = new_tail;
	if ( new_tail == (struct dict_node *)0 )
	{
	    curr       = names_dict;
	    names_dict = (struct dict_node *)0;
	}
	else
	{
	    curr	   = new_tail->next;
	    new_tail->next = (struct dict_node *)0;
	}

	for ( ; curr != (struct dict_node *)0; curr = next )
	{
	    next = curr->next;
	    free((char *)curr->name);
	    free(curr);
	}
    }
}

#line 159 "vars.nw"
void
cleanup_names()
{
    struct dict_node *prev, *curr, *next;
    Choicepoint	     *cp;

    /* Phase I: reverse the dictionary */
    prev = (struct dict_node *)0;
    for ( curr = names_dict; curr != (struct dict_node *)0; curr = next )
    {
	next	   = curr->next;
	curr->next = prev;
	prev	   = curr;
    }

    /* Phase II: update the control stack */
    for ( cp = bp; cp != (Choicepoint *)0; cp = cp->btBp )
    {
	curr = cp->btDict;
	while ( curr != (struct dict_node *)0 && curr->node == (Node *)0 )
	    curr = curr->next;
	cp->btDict = curr;
    }

    /* Phase III: re-reverse the dictionary and release unused nodes */
    curr = prev;
    prev = (struct dict_node *)0;
    for ( ; curr != (struct dict_node *)0; curr = next )
    {
	next = curr->next;
	if ( curr->node == (Node *)0 )
	{
	    free((char *)curr->name);
	    free(curr);
	}
	else
	{
	    curr->next = prev;
	    prev       = curr;
	}
    }
    names_dict = prev;
}

#line 213 "vars.nw"
static const char *gen_name(void);

extern const char *lookup_name(Node *node)
{
    const char	     *name;
    struct dict_node *dict;

    for ( dict = names_dict; dict != (struct dict_node *)0; dict = dict->next )
	if ( dict->node == node )
	    return dict->name;

    name = gen_name();
    add_name(node, name);
    return name;
}

#line 242 "vars.nw"
static unsigned long dict_index;

static const char *
gen_name()
{
    char name[13];

    name[0] = '_';
    name[1] = 'a' + dict_index % 26;
    if ( dict_index < 26 )
	name[2] = '\0';
    else
	sprintf(name + 2, "%ld", dict_index / 26);
    dict_index++;

    return (const char *)strdup(name);
}
