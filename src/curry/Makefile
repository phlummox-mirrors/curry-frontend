
# MCC prelude
PRELUDE_CURRY  	= prelude.curry
PRELUDE_INTF   	= $(PRELUDE_CURRY:%.curry=%.icurry)
PRELUDE_FLAT   	= $(PRELUDE_CURRY:%.curry=%.flat)

# MCC library
LIB_CURRY	= 

# The following variables are exported by top level makefile
# MCC_PATH	- root path of the MCC

# path to the curry library
MCC_LIB_CURRY = $(MCC_PATH)/lib/curry

# The compiler "cyc"
CYC           = $(MCC_PATH)/bin/cyc


#------------------------------------------------------------------------------
# Let's start...

.PHONY: all

all: compile install


# compile the curry library files
.PHONY: compile

compile: $(PRELUDE_INTF) $(PRELUDE_FLAT)

$(PRELUDE_INTF): $(PRELUDE_CURRY)
	$(CYC) --flat $<

$(PRELUDE_FLAT): $(PRELUDE_CURRY)
	$(CYC) --flat $<


# install the curry library files
.PHONY: install

install: $(PRELUDE_INTF) $(PRELUDE_FLAT)
	@cp ./*.curry $(MCC_LIB_CURRY)/
	@cp ./*.icurry $(MCC_LIB_CURRY)/
	@cp ./*.flat $(MCC_LIB_CURRY)/

