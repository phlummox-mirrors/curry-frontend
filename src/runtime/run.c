#line 147 "run.nw"
#include "config.h"
#include <setjmp.h>
#include "run.h"

static jmp_buf halt_buf;

#if USE_TRAMPOLINE
void
run(Label ip)
{
    if ( setjmp(halt_buf) == 0 )
    {
	while ( 1 )
	{
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	    ip = (Label)(*ip)();
	}
    }
}
#endif /* USE_TRAMPOLINE */

#line 188 "run.nw"
#if !USE_TRAMPOLINE
# if __GNUC__ == 2 && __GNUC_MINOR__ == 91 && defined(__sparc)
/* needed to work around an instruction scheduler bug in gcc 2.91 for sparc */
Label ip;
# endif

static void do_run(Label ip);

void
run(Label ip)
{
    if ( setjmp(halt_buf) == 0 )
	do_run(ip);
}

static void
do_run(Label ip)
{
    char dummy[C_STACK_SIZE];

    /* hack to avoid unused variable warning */
    __asm__("" : : "g"(dummy));

    goto *ip;
}
#endif /* !USE_TRAMPOLINE */

#line 221 "run.nw"
void
halt()
{
    longjmp(halt_buf, 1);
}
