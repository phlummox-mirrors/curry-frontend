#line 9 "heap.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "run.h"
#include "heap.h"
#include "eval.h"

#line 167 "heap.nw"
const int ot_binary[] = { 0 };

#line 231 "heap.nw"
NodeInfo ___91__93__info = {
    NIL_TAG, nil_node_size, (const int *)0, (Label)eval_whnf, "[]", (FinalFun)0
};
NodeInfo ___58__info = {
    CONS_TAG, cons_node_size, (const int *)0, (Label)eval_whnf, ":", (FinalFun)0
};
NodeInfo ___40__41__info = {
    UNIT_TAG, unit_node_size, (const int *)0, (Label)eval_whnf, "()", (FinalFun)0
};
NodeInfo __Success_info = {
    SUCCESS_TAG, success_node_size, (const int *)0, (Label)eval_whnf, "Success",
    (FinalFun)0
};

NodeInfo *___91__93__node = &___91__93__info;
NodeInfo *___40__41__node = &___40__41__info;
NodeInfo *__Success_node  = &__Success_info;

boolean
is_tuple(const NodeInfo *info)
{
    const char *cp = info->cname;

    if ( *cp++ != '(' || *cp++ != ',' )
	return false;
    while ( *cp == ',' )
	cp++;
    return *cp++ == ')' && *cp == '\0';
}

boolean
is_operator(const NodeInfo *info)
{
    const char *cp;

    if ( info == &___91__93__info || info == &___40__41__info )
	return false;

    for ( cp = info->cname; *cp != '\0'; cp++ )
    {
	if ( *cp == '.' )
	    cp++;
	if ( !isalnum(*cp) && *cp != '\'' && *cp != '_' )
	    return true;
	else if ( *cp == '_' )
	{
	    if ( cp[1] == '#' )
		cp++;
	    else if ( strncmp(cp + 1, "debug#", 6) )
		cp += 6;
	}
    }
    return false;
}

#line 360 "heap.nw"
#if ONLY_BOXED_OBJECTS
NodeInfo int_info = { 
    INT_TAG, int_node_size, ot_binary, (Label)eval_whnf, (const char *)0, (FinalFun)0
};
#endif

#line 438 "heap.nw"
NodeInfo char_info = {
    CHAR_TAG, char_node_size, ot_binary, (Label)eval_whnf, (const char *)0,
    (FinalFun)0
};

struct char_node char_table[256];

void
init_chars()
{
    int i;

    for (i = 0; i < 256; i++ )
    {
	char_table[i].info = &char_info;
	char_table[i].ch = i;
    }
}

#line 515 "heap.nw"
NodeInfo variable_info = {
    VARIABLE_TAG, variable_node_size, (const int *)0, (Label)eval_whnf,
    (const char *)0, (FinalFun)0
};

#line 562 "heap.nw"
NodeInfo queueMe_info = {
    QUEUEME_TAG, queueMe_node_size, (const int *)0, (Label)eval_queueMe,
    (const char *)0, (FinalFun)0
};

#line 601 "heap.nw"
NodeInfo indir_info = {
    INDIR_TAG, indir_node_size, (const int *)0, (Label)eval_indir, (const char *)0,
    (FinalFun)0
};
NodeInfo suspend_indir_info = {
    INDIR_TAG, suspend_node_size, (const int *)0, (Label)eval_indir, (const char *)0,
    (FinalFun)0
};
NodeInfo variable_indir_info = {
    INDIR_TAG, variable_node_size, (const int *)0, (Label)eval_indir, (const char *)0,
    (FinalFun)0
};

#line 632 "heap.nw"
NodeInfo search_cont_info = {
    SEARCH_CONT_TAG, search_cont_node_size, (const int *)0, (Label)no_eval,
    "<state>", (FinalFun)0
};

#line 674 "heap.nw"
word *hp;
word *hlim;
word *heap_base;
word *heap_end;

#line 415 "heap.nw"
NodeInfo float_info = {
    FLOAT_TAG, float_node_size, ot_binary, (Label)eval_whnf, (const char *)0,
    (FinalFun)0
};


#line 699 "heap.nw"
boolean in_gc = false;

#line 731 "heap.nw"
Node	   **local_roots;
GlobalRoot *global_roots;

#line 785 "heap.nw"
void
add_global_root(Node **root)
{
    GlobalRoot *head;

    head = (GlobalRoot *)malloc(sizeof(GlobalRoot));
    if ( head == (GlobalRoot *)0 )
    {
	fprintf(stderr, "Out of memory in add_global_root\n");
	exit(1);
    }

    head->next	 = global_roots;
    head->root	 = root;
    global_roots = head;
}

void
remove_global_root(Node **root)
{
    GlobalRoot *prev, *curr;

    for ( prev = (GlobalRoot *)0, curr = global_roots;
	  curr != (GlobalRoot *)0;
	  prev = curr, curr = curr->next )
	if ( curr->root == root )
	{
	    if ( prev != (GlobalRoot *)0 )
		prev->next = curr->next;
	    else
		global_roots = curr->next;
	    free(curr);
	    return;
	}

    fprintf(stderr, "remove_global_root: %p not registered as a root\n", root);
    exit(1);
}

#line 860 "heap.nw"
void
heap_exhausted()
{
    fprintf(stderr,
	    "not enough free memory in heap after garbage collection\n");
    exit(1);
}
