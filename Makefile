#------------------------------------------------------------------------------
#--
#-- Generate a simple version of the Muenster Curry Compiler for
#-- running with PAKCS
#--


# Path of the MCC
MCC	 = $(CURDIR)

MCC_SRC  = $(MCC)/src
MCC_BIN  = $(MCC)/bin
MCC_DIST = $(MCC)/dist

# distribution
MCC_DIST_NAME = mcc_for_pakcs


#------------------------------------------------------------------------------
# Let's start...

# Generate the MCC
.PHONY: all

all: compile


# Compile all necessary MCC components
.PHONY: compile

compile:
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
	@cp $(MCC_BIN)/cymake $(MCC_DIST)/mcc/bin/
	@cp $(MCC)/LIESMICH $(MCC_DIST)/mcc
	@cp $(MCC)/LICENSE $(MCC_DIST)/mcc

	@cd $(MCC_DIST)  && tar cvf $(MCC_DIST_NAME).tar mcc/*		\
			 && gzip -f9 -S .gz $(MCC_DIST_NAME).tar
