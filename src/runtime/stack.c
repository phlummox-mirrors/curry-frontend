#line 26 "stack.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "main.h"

Node **stack_base;
Node **stack_end;
Node **sp;

#line 47 "stack.nw"
void
init_stack(unsigned int stack_size)
{
    stack_size = (stack_size + pagemask) & ~pagemask;
    stack_base = (Node **)malloc(stack_size + pagemask);
    if ( stack_base == (Node **)0 )
    {
	fprintf(stderr, "not enough memory to allocate stack\n");
	exit(1);
    }

    stack_base = (Node **)(((long)stack_base + pagemask) & ~pagemask); 
    stack_end  = stack_base + stack_size / word_size;
    sp	       = stack_end;
}

#line 78 "stack.nw"
void
stack_overflow()
{
    fprintf(stderr, "stack overflow, re-run program with a larger stack\n");
    exit(1);
}

#line 116 "stack.nw"
Choicepoint *bp;

#line 157 "stack.nw"
Label *choice_conts;

struct nondet_handlers nondet_handlers;

#line 190 "stack.nw"
ExceptionFrame *efp;
