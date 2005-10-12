
# the command line compiler 'cymake'
CYMAKE     = cymake

# the haskell compiler
HC         = ghc
HC_OPTS	   = -v1 -syslib lang --make


# MCC paths

MCC_SRC = $(CURDIR)
MCC     = $(MCC_SRC)/..

# path to the mcc binaries
MCC_BIN  	= $(MCC)/bin


#------------------------------------------------------------------------------
# Let's start...


# Compile all MCC components
.PHONY: all

all: src install


# Compile MCC components and generate "cymake"
.PHONY: src

src:
	$(HC) $(HC_OPTS) $(CYMAKE) -o $(CYMAKE)


# Install the compiler
.PHONY: install


install: $(CYMAKE)
	@mv ./$(CYMAKE) $(MCC_BIN)/
