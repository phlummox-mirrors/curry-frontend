#------------------------------------------------------------------------------
#--
#-- Generate a simple version of the Muenster Curry Compiler for
#-- running with PAKCS
#--


# Paths of the MCC
export MCC_PATH		= $(CURDIR)

MCC_SRC  = $(MCC_PATH)/src
MCC_BIN  = $(MCC_PATH)/bin
MCC_LIB  = $(MCC_PATH)/lib
MCC_DIST = $(MCC_PATH)/dist

# distribution
MCC_DIST_NAME = mcc_for_pakcs-082005


#------------------------------------------------------------------------------
# Let's start...

# Generate the MCC
.PHONY: all

all: compile


# Compile all necessary MCC components
.PHONY: compile

compile:
	@export MCC=$(MCC_PATH)
	@cd $(MCC_SRC) && make

# Clean object files
.PHONY: clean
clean:
	@cd $(MCC_SRC) && rm -f *.hi *.o


# Generate distribution
.PHONY: dist

dist: compile mk_dist

mk_dist: 
	@mkdir -p $(MCC_DIST)/mcc/bin
	@mkdir -p $(MCC_DIST)/mcc/lib/runtime

	@cp $(MCC_LIB)/runtime/cycc $(MCC_DIST)/mcc/lib/runtime
	@cp $(MCC_LIB)/runtime/cymk $(MCC_DIST)/mcc/lib/runtime
	@cp $(MCC_LIB)/runtime/smake $(MCC_DIST)/mcc/lib/runtime
	@cp $(MCC_BIN)/cyc $(MCC_DIST)/mcc/bin/
	@cp $(MCC_BIN)/cymake $(MCC_DIST)/mcc/bin/
	@cp $(MCC_PATH)/LIESMICH $(MCC_DIST)/mcc
	@cp $(MCC_PATH)/LICENSE $(MCC_DIST)/mcc

	@cd $(MCC_DIST)  && tar cvf $(MCC_DIST_NAME).tar mcc/*		\
			 && gzip -f9 -S .gz $(MCC_DIST_NAME).tar
