
# runtime components of the Muenster Curry Compiler
RTS_H	   = curry.h debug.h run.h heap.h stack.h threads.h spaces.h eval.h  \
             trail.h backtrack.h search.h io_monad.h unify.h disequal.h      \
             char.h cstring.h files.h print.h vars.h main.h cam.h trace.h    \
	     stats.h
RTS_C      = run.c heap.c gc_2space.c stack.c threads.c spaces.c eval.c      \
             trail.c backtrack.c search.c io_monad.c constraints.c           \
	     unify.c disequal.c compare.c char.c int.c float.c cstring.c     \
	     files.c directory.c time.c system.c random.c refs.c vector.c    \
	     show.c print.c vars.c main.c trace.c stats.c
RTS_O	   = $(RTS_C:%.c=%.o)

GCCOMP_C   = gc_compact.c
GCCOMP_O   = gc_compact.o

LIBCURRY   = libcurry.a

CONFIG_H   = config.h

# the c compiler
CC	   = gcc
CCFLAGS	   =  -g -O2 -Wall -fno-defer-pop

# the archiving tool
AR	   = ar
ARFLAGS	   = sr


# The following variables are exported by top level makefile
# MCC_PATH	- root path of the MCC

MCC_LIB_RUNTIME = $(MCC_PATH)/lib/runtime

#------------------------------------------------------------------------------
# Let's start...


# Generate all runtime components
.PHONY: all

all: rts libc install


# Compile runtime components
.PHONY: rts

rts: $(RTS_O) $(GCCOMP_O)

$(RTS_O): %.o: %.c $(RTS_C)
	$(CC) $(CCFLAGS) -c $< -o $@

$(GCCOMP_O): $(GCCOMP_C)
	$(CC) $(CCFLAGS) -c $< -o $@


# Generate the library archiv
.PHONY: libc

libc: $(LIBCURRY)

$(LIBCURRY): $(RTS_O)
	$(AR) $(ARFLAGS) $(LIBCURRY) $(RTS_O)


# Install the runtime components
.PHONY: install

install: $(RTS_O) $(GCCOMP_O) $(LIBCURRY)
	@cp ./*.h $(MCC_LIB_RUNTIME)
	@cp ./$(GCCOMP_O) $(MCC_LIB_RUNTIME)/
	@cp ./$(LIBCURRY) $(MCC_LIB_RUNTIME)/


