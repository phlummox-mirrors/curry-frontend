#line 40 "run.nw"
#if !USE_TRAMPOLINE
# ifndef __GNUC__
#  error "direct jumps require Gnu C; reconfigure with --enable-trampoline"
# endif
#endif

#if USE_TRAMPOLINE
typedef void *(*Label)(void);
#else
typedef void *Label;
#endif

#line 79 "run.nw"
#if USE_TRAMPOLINE

# define FUNCTION(f)		void *f(void)
# define DECLARE_ENTRYPOINT(l)	extern void *l(void)
# define DECLARE_LABEL(l)       static void *l(void)
# define EXPORT_LABEL(l)
# define ENTRY_LABEL(l)

# define GOTO(l)		return (void *)(l)

#else /* !USE_TRAMPOLINE */

# define C_STACK_SIZE 8192

# if __GNUC__ > 2 || __GNUC__ == 2 && __GNUC_MINOR__ > 7
#  define stringify_value(x) stringify(x)
#  define stringify(x)       #x
#  if defined(__i386)
#   define SP_OFFSET (-C_STACK_SIZE+(C_STACK_SIZE+8)%%16)
#   define SP_HACK "leal " stringify_value(SP_OFFSET) "(%%ebp),%%esp\n"
#  endif
# endif
# ifndef SP_HACK
#  define SP_HACK
# endif

# define FUNCTION(f)		void _FUNC(f)(void)
# define DECLARE_ENTRYPOINT(l) \
    void _FUNC(l)(void); \
    void l(void) __asm__(_ENTRY_LABEL(l))
# define DECLARE_LABEL(l) \
    static void _FUNC(l)(void); \
    void l(void) __asm__(_ENTRY_LABEL(l))
# define _FUNC(f) f##_func
# define EXPORT_LABEL(l)	__asm__(" .globl " _ENTRY_LABEL(l) "\n");
# define ENTRY_LABEL(l)	\
 	__asm__(_ENTRY_LABEL(l) ":" SP_HACK : : "g" (_FUNC(l)));
# define _ENTRY_LABEL(l)	#l "_entry"

# if __GNUC__ == 2 && __GNUC_MINOR__ == 91 && defined(__sparc)
/* work around an instruction scheduler bug in gcc 2.91 for sparc */
extern Label ip;
#  define GOTO(l) do { ip = (Label)(l); goto *ip; } while ( 0 )
# else
#  define GOTO(l) goto *(Label)(l)
# endif

#endif /* !USE_TRAMPOLINE */

#line 134 "run.nw"
extern void run(Label ip);
extern void halt(void) __attribute__ ((noreturn));

