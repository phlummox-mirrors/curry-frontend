#line 45 "gc_2space.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "trail.h"
#include "threads.h"
#include "spaces.h"
#include "vars.h"
#include "stats.h"
#include "main.h"

#line 177 "gc_2space.nw"
#define GC_FLAGS                0x03
#define FORWARD_FLAG            0x01
#define is_forwarded(node)      ((*(unsigned int *)(node)) & FORWARD_FLAG)
#define forward(node,new) \
    ((*(unsigned int *)(node)) = (unsigned int)(new) | FORWARD_FLAG)
#define get_forward(node)       ((Node *)(*(unsigned int *)(node) & ~GC_FLAGS))

#line 194 "gc_2space.nw"
#define GC_copy(node) do { \
    if ( is_boxed(node) && (node) >= (Node *)heap_base && (node) < (Node *)hp ) { \
        if ( is_forwarded(node) ) \
            node = get_forward(node); \
        else { \
            unsigned int sz = node_size(node); \
	    if ( sz == 0 ) sz = (node)->a.length; \
            ASSERT((word *)copy + sz <= to_space + heap_size); \
            memcpy(copy, (node), sz * word_size); \
            forward(node, copy); \
            (node) = (Node *)copy; \
            copy += sz; \
        } \
    } \
} while ( 0 )


#line 62 "gc_2space.nw"
static word *from_space;
static word *to_space;
static unsigned long heap_size;

void
init_heap(unsigned long size)
{
    heap_size = (size + pagemask) & ~pagemask;
    heap_base = (word *)malloc(2 * heap_size + pagemask);
    if ( heap_base == (word *)0 )
    {
        fprintf(stderr, "not enough memory to allocate heap\n");
        exit(1);
    }

    heap_base  = (word *)(((long)heap_base + pagemask) & ~pagemask);
    heap_size /= word_size;
    from_space = heap_base;
    to_space   = from_space + heap_size;
    heap_end   = to_space;
    hp = hlim  = heap_base;
}

#line 99 "gc_2space.nw"
static unsigned int n_finals, max_finals;
static Node	    **finals;

void
register_final(Node *fin)
{
    ASSERT(fin->info->final_fun != (FinalFun)0);

    if ( n_finals == max_finals )
    {
	max_finals += 1024;
	if ( finals == (Node **)0 )
	    finals = (Node **)malloc(max_finals * sizeof(Node *));
	else
	    finals = (Node **)realloc(finals, max_finals * sizeof(Node *));
	if ( finals == (Node **)0 )
	{
	    fprintf(stderr,
		    "Not enough memory to extend final table to %u entries\n",
		    max_finals);
	    exit(1);
	}
    }

    finals[n_finals++] = fin;
}

#line 133 "gc_2space.nw"
void
collect(unsigned int request)
{
    unsigned int     i, j, len;
    word	     *aux;
    Node	     **scan, **copy, **lroots;
    GlobalRoot	     *groots;
    Choicepoint	     *cp, *prev_cp, *next_cp;
    struct dict_node *dict;

    stats_begin_gc(hp - heap_base);
    in_gc = true;
    copy  = (Node **)to_space;
    
#line 217 "gc_2space.nw"
for ( groots = global_roots; groots != (GlobalRoot *)0; groots = groots->next )
    GC_copy(*groots->root);
for ( lroots = local_roots; lroots != (Node **)0; lroots = (Node **)lroots[1] )
{
    for ( i = (unsigned)lroots[0], scan = (Node **)lroots + 2;
          i > 0;
          i--, scan++ )
        GC_copy(*scan);
}

#line 237 "gc_2space.nw"
prev_cp = next_cp = (Choicepoint *)0;
for ( cp = bp; cp != (Choicepoint *)0; cp = prev_cp )
{
    prev_cp  = cp->btBp;
    cp->btBp = next_cp;
    next_cp  = cp;
}

scan = stack_end;
for ( cp = next_cp; cp != (Choicepoint *)0; cp = next_cp )
{
    while ( --scan >= (Node **)(cp + 1) )
	GC_copy(*scan);

    GC_copy((Node *)cp->btRq);

    next_cp  = cp->btBp;
    cp->btBp = prev_cp;
    prev_cp  = cp;
    scan     = (Node **)cp;
}
while ( --scan >= sp )
    GC_copy(*scan);

#line 266 "gc_2space.nw"
{
    SaveRec *scan_trail;

    for ( scan_trail = trail_base; scan_trail != tp; scan_trail++ )
    {
        GC_copy((Node *)scan_trail->addr);
        GC_copy((Node *)scan_trail->val);
    }
}

#line 280 "gc_2space.nw"
GC_copy((Node *)rq);
GC_copy((Node *)ss);

#line 147 "gc_2space.nw"
    
#line 289 "gc_2space.nw"
for ( scan = (Node **)to_space; scan != copy; scan += len )
{
    boolean   is_vect;
    int       n, el_len;
    NodeInfo  *info;
    const int *otable;

    ASSERT(!is_forwarded(scan));
    info    = ((Node *)scan)->info;
    len     = info->length;
    otable  = info->offset_table;
    is_vect = len == 0;
    if ( is_vect )
	len = (int)scan[1];

    if ( otable == (const int *)0 )
    {
	for ( i = is_vect ? 2 : 1 ; i < len; i++ )
	    GC_copy(scan[i]);
    }
    else
    {
	n = *otable++;
	if ( n >= 0 )
	{
	    while ( n-- > 0 )
	    {
		i = *otable++;
		GC_copy(scan[i]);
	    }
	}
	else
	{
	    ASSERT(is_vect);
	    el_len = -n;
	    for ( j = 2; j < len; j += el_len )
	    {
		otable = info->offset_table + 1;
		n      = *otable++;
		while ( n-- > 0 )
		{
		    i = *otable++;
		    GC_copy(scan[j+i]);
		}
	    }
	    ASSERT(j == len);
	}
    }
}

#line 148 "gc_2space.nw"
    
#line 362 "gc_2space.nw"
for ( dict = names_dict; dict != (struct dict_node *)0; dict = dict->next )
    if ( is_forwarded(dict->node) )
	dict->node = get_forward(dict->node);
    else
	dict->node = (Node *)0;

#line 149 "gc_2space.nw"
    
#line 348 "gc_2space.nw"
for ( i = j = 0; i < n_finals; i++ )
    if ( is_forwarded(finals[i]) )
	finals[j++] = get_forward(finals[i]);
    else
	finals[i]->info->final_fun(finals[i]);
n_finals = j;

#line 150 "gc_2space.nw"
    
#line 87 "gc_2space.nw"
aux = from_space; from_space = to_space; to_space = aux;
heap_base = from_space; heap_end = from_space + heap_size;

#line 151 "gc_2space.nw"
    hp = (word *)copy;
    if ( bp != (Choicepoint *)0 )
    {
	hlim = hp;
	for ( cp = bp; cp != (Choicepoint *)0; cp = cp->btBp )
	    cp->btHp = hp;
    }
    else
    {
        ASSERT(hlim == to_space);
        hlim = heap_base;
    }
    if ( hp + request >= heap_end )
        heap_exhausted();
    cleanup_names();
    in_gc = false;
    stats_end_gc(hp - heap_base);
}

#line 383 "gc_2space.nw"
void
release_mem()
{
    unsigned int i = n_finals;

    while ( i-- > 0 && (word *)finals[i] >= hlim )
    {
	ASSERT((word *)finals[i] < hp);
	finals[i]->info->final_fun(finals[i]);
    }
    n_finals = ++i;

    stats_backtrack(hp - hlim);
    hp = hlim;
}
