#line 13 "gc_compact.nw"
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

#line 85 "gc_compact.nw"
#define GC_FLAGS		0x03
#define MARK_FLAG		0x01
#define PTR_FLAG		0x02

#define is_marked(node)		((*(unsigned int *)(node)) & MARK_FLAG)
#define is_unmarked(node)	!is_marked(node)
#define mark_node(node)		((*(unsigned int *)(node)) |= MARK_FLAG)
#define unmark_node(node)	((*(unsigned int *)(node)) &= ~MARK_FLAG)

#define is_threaded(node)	((*(unsigned int *)(node)) & PTR_FLAG)

#line 108 "gc_compact.nw"
static void mark(Node *node);

#define GC_mark(node) do { \
    if ( is_boxed(node) && (word *)(node) >= heap_base && (word *)(node) < hp ) { \
	if ( is_unmarked(node) ) mark((Node *)node); \
	if ( is_downward_pointer(node) ) thread_pointer(node); \
    } \
} while ( 0 )

#define is_downward_pointer(node) \
    ((word *)&(node) >= (word *)(node) || (word *)&(node) < heap_base)
#define is_upward_pointer(node) \
    ((word *)&(node) < (word *)(node) && (word *)(node) < hp)

#line 130 "gc_compact.nw"
#define thread_pointer(p) do { \
    unsigned int *q = (unsigned int *)(p); \
    *(Node **)&(p) = (Node *)*q; \
    *q = (unsigned int)&(p) | (MARK_FLAG|PTR_FLAG); \
} while ( 0 )

#line 144 "gc_compact.nw"
#define unthread_pointer(node,free) do { \
    unsigned int *q = \
        (unsigned int *)(*(unsigned int *)(node) & ~(MARK_FLAG|PTR_FLAG)); \
    *(unsigned int *)(node) = *q; *q = (unsigned int)(free); \
} while ( 0 )


#line 30 "gc_compact.nw"
void
init_heap(unsigned long heap_size)
{
    heap_base = (word *)malloc(heap_size + pagemask);
    if ( heap_base == (word *)0 )
    {
	fprintf(stderr, "not enough memory to allocate heap\n");
	exit(1);
    }
    heap_base = (word *)(((long)heap_base + pagemask) & ~pagemask);
    heap_end  = heap_base + heap_size / word_size;
    hp = hlim = heap_base;
}

void
collect(unsigned int request)
{
    unsigned int     i, heap_limit = 0;
    Node	     **scan, **free, **lroots;
    GlobalRoot	     *groots;
    Choicepoint	     *cp;
    struct dict_node *dict;

    stats_begin_gc(hp - heap_base);
    in_gc = true;
    
#line 155 "gc_compact.nw"
for ( groots = global_roots; groots != (GlobalRoot *)0; groots = groots->next )
    GC_mark(*groots->root);
for ( lroots = local_roots; lroots != (Node **)0; lroots = (Node **)lroots[1] )
{
    for ( i = (unsigned int)lroots[0], scan = (Node **)lroots + 2;
	  i > 0;
	  i--, scan++ )
	GC_mark(*scan);
}

#line 173 "gc_compact.nw"
scan = sp;
for ( cp = bp; cp != (Choicepoint *)0; cp = cp->btBp )
{
    GC_mark(cp->btRq);
    for ( ; scan < (Node **)cp; scan++ )
	GC_mark(*scan);
    scan = (Node **)(cp + 1);
}
for ( ; scan < stack_end; scan++ )
    GC_mark(*scan);

#line 189 "gc_compact.nw"
{
    SaveRec *scan_trail;

    for ( scan_trail = trail_base; scan_trail != tp; scan_trail++ )
    {
        GC_mark(scan_trail->addr);
        GC_mark(scan_trail->val);
    }
}

#line 203 "gc_compact.nw"
GC_mark(rq);
GC_mark(ss);

#line 277 "gc_compact.nw"
{
    unsigned int sz;

    for ( cp = bp; cp != (Choicepoint *)0; cp = cp->btBp )
	if ( cp->btHp != 0 )
	{
	    while ( cp->btHp < hp && is_unmarked(cp->btHp) )
	    {
		sz = node_size((Node *)cp->btHp);
		if ( sz == 0 )
		    sz = ((Node *)cp->btHp)->a.length;
		cp->btHp += sz;
	    }
	    ASSERT(cp->btHp <= hp);
	    if ( cp->btHp == hp )
	        cp->btHp = (word *)&heap_limit;
	    thread_pointer(cp->btHp);
	}
}

#line 56 "gc_compact.nw"
    
#line 312 "gc_compact.nw"
for ( dict = names_dict; dict != (struct dict_node *)0; dict = dict->next )
    if ( is_marked(dict->node) )
	thread_pointer(dict->node);
    else
	dict->node = (Node *)0;

#line 57 "gc_compact.nw"
    
#line 331 "gc_compact.nw"
scan = free = (Node **)heap_base;
while ( (word *)scan < hp )
{
    boolean	 is_vect;
    int		 n, el_len;
    unsigned int j, len;
    NodeInfo	 *info;
    const int	 *otable;

    if ( is_marked((Node *)scan) )
    {
	while ( is_threaded((Node *)scan) )
	    unthread_pointer(scan, free);
	unmark_node((Node *)scan);

	info	= ((Node *)scan)->info;
	len	= info->length;
	is_vect = len == 0;
	if ( is_vect )
	    len = (int)scan[1];
	memcpy(free, scan, len * word_size);

	
#line 385 "gc_compact.nw"
otable = info->offset_table;
if ( otable == (const int *)0 )
{
    for ( i = is_vect ? 2 : 1; i < len; i++ )
    {
	if ( is_boxed(free[i]) && is_upward_pointer(free[i]) )
	    thread_pointer(free[i]);
    }
}
else
{
    n = *otable++;
    if ( n >= 0 )
    {
	while ( n-- > 0 )
	{
	    i = *otable++;
	    if ( is_boxed(free[i]) && is_upward_pointer(free[i]) )
		thread_pointer(free[i]);
	}
    }
    else
    {
	el_len = -n;
	for ( j = 2; j < len; j += el_len )
	{
	    otable = info->offset_table + 1;
	    n      = *otable++;
	    while ( n-- > 0 )
	    {
		i = *otable++;
		if ( is_boxed(free[j+i]) && is_upward_pointer(free[j+i]) )
		    thread_pointer(free[j+i]);
	    }
	}
    }
}


#line 355 "gc_compact.nw"
	scan += len;
	free += len;
    }
    else
    {
	info	= ((Node *)scan)->info;
	len	= info->length;
	is_vect = len == 0;
	if ( is_vect )
	    len = (int)scan[1];
	if ( info->final_fun != (FinalFun)0 )
	    info->final_fun((Node *)scan);
	scan += len;
    }
}
ASSERT((word *)scan == hp);

#line 377 "gc_compact.nw"
while ( heap_limit != 0 )
    unthread_pointer(&heap_limit, free);

#line 58 "gc_compact.nw"
    hp	 = (word *)free;
    hlim = bp != (Choicepoint *)0 ? bp->btHp : heap_base;
    if ( hp + request >= heap_end )
	heap_exhausted();
    cleanup_names();
    in_gc = false;
    stats_end_gc(hp - heap_base);
}

#line 74 "gc_compact.nw"
void
register_final(Node *fin)
{
}

#line 212 "gc_compact.nw"
static void
mark(Node *node)
{
    boolean	 is_vect;
    unsigned int i, j, len;
    int		 n, el_len;
    Node	 **scan;
    NodeInfo	 *info;
    const int	 *otable;

    scan    = (Node **)node;
    info    = node->info;
    len	    = info->length;
    otable  = info->offset_table;
    is_vect = len == 0;
    if ( is_vect )
	len = (int)scan[1];

    mark_node(node);

    if ( otable == (const int *)0 )
    {
	for ( i = is_vect ? 2 : 1; i < len; i++ )
	    GC_mark(scan[i]);
    }
    else
    {
	n = *otable++;
	if ( n >= 0 )
	{
	    while ( n-- > 0 )
	    {
		i = *otable++;
		GC_mark(scan[i]);
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
		    GC_mark(scan[j+i]);
		}
	    }
	    ASSERT(j == len);
	}
    }
}

#line 430 "gc_compact.nw"
void
release_mem()
{
    unsigned int sz;
    Node	 *scan;

    for ( scan = (Node *)hlim; (word *)scan < hp; (word *)scan += sz )
    {
	if ( scan->info->final_fun != (FinalFun)0 )
	    scan->info->final_fun(scan);
	sz = node_size(scan);
	if ( sz == 0 )
	    sz = ((Node *)scan)->a.length;
    }

    stats_backtrack(hp - hlim);
    hp = hlim;
}
