#------------------------------------------------------------------------------
#--
#-- Generate a simple version of the Muenster Curry Compiler for
#-- running with PAKCS
#--


# Paths of the MCC
export MCC_PATH		= $(CURDIR)

#------------------------------------------------------------------------------
# Let's start...

# Generate the MCC
.PHONY: all

all: compile


# Compile all necessary MCC components
.PHONY: compile

compile:
	@export MCC=$(MCC_PATH)
	@cd $(MCC_PATH)/src && make

