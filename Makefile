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

MCC_DIST_BIN = $(MCC_DIST)/binary
MCC_DIST_SRC = $(MCC_DIST)/source

# distributions
MCC_SRC_NAME = mcc_for_pakcs_src
MCC_BIN_NAME = mcc_for_pakcs_`uname -s`


#------------------------------------------------------------------------------
# Let's start...

# Generate the MCC
.PHONY: all

all: compile

# Compile all necessary MCC components
.PHONY: compile

compile:
	@cd $(MCC_SRC) && ./testghc.sh && make

# Clean generated files
.PHONY: clean

clean: clean_src clean_dist

clean_src:
	@cd $(MCC_SRC) && rm -f *.hi *.o

clean_dist:
	@cd $(MCC_DIST) && rm -rf *


# Generate distribution

# name of the root directory of the distribution:
DISTROOT=mccparser

.PHONY: dist

dist: compile dist_src dist_bin

dist_src:
	@mkdir -p $(MCC_DIST_SRC)/$(DISTROOT)/src
	@mkdir -p $(MCC_DIST_SRC)/$(DISTROOT)/bin
	@mkdir -p $(MCC_DIST_SRC)/$(DISTROOT)/dist
	@cp $(MCC_SRC)/*.lhs $(MCC_DIST_SRC)/$(DISTROOT)/src
	@cp $(MCC_SRC)/*.hs $(MCC_DIST_SRC)/$(DISTROOT)/src
	@cp $(MCC_SRC)/Makefile $(MCC_DIST_SRC)/$(DISTROOT)/src
	@cp $(MCC_SRC)/testghc.sh $(MCC_DIST_SRC)/$(DISTROOT)/src
	@cp $(MCC)/LICENSE $(MCC_DIST_SRC)/$(DISTROOT)
	@cp $(MCC)/Makefile $(MCC_DIST_SRC)/$(DISTROOT)

	@cd $(MCC_DIST_SRC)                               \
		&& tar cvf $(MCC_SRC_NAME).tar $(DISTROOT)/*      \
		&& gzip -f9 -S .gz $(MCC_SRC_NAME).tar    \
		&& mv $(MCC_SRC_NAME).tar.gz $(MCC_DIST)
	@rm -rf $(MCC_DIST_SRC)

dist_bin:
	@mkdir -p $(MCC_DIST_BIN)/$(DISTROOT)/bin
	@cp $(MCC_BIN)/cymake $(MCC_DIST_BIN)/$(DISTROOT)/bin
	@cp $(MCC)/LICENSE $(MCC_DIST_BIN)/$(DISTROOT)

	@cd $(MCC_DIST_BIN)                               \
		&& tar cvf $(MCC_BIN_NAME).tar $(DISTROOT)/*      \
		&& gzip -f9 -S .gz $(MCC_BIN_NAME).tar    \
		&& mv $(MCC_BIN_NAME).tar.gz $(MCC_DIST)
	@rm -rf $(MCC_DIST_BIN)
