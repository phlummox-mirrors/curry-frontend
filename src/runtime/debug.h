#line 12 "debug.nw"
#ifdef DEBUG
# ifdef NDEBUG
#  undef NDEBUG
# endif

# include <assert.h>
# define ASSERT(e) assert(e)
#else
# define ASSERT(e)
#endif
