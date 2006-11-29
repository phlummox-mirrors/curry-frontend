
# the command line compiler 'cymake'
CYMAKE     = cymake

# the frontend api
FRONTEND_HS = Frontend.hs

# the haskell compiler
HC         = ghc
HC_OPTS	   = -v1 -syslib lang --make -O2 -fvia-C 


# MCC paths

MCC_SRC = $(CURDIR)
MCC     = $(MCC_SRC)/..

# path to the mcc binaries
MCC_BIN  	= $(MCC)/bin


#------------------------------------------------------------------------------
# Let's start...


# Compile all MCC components
.PHONY: all

all: src frontend install


# Compile MCC components and generate "cymake"
.PHONY: src

src:
	$(HC) $(HC_OPTS) $(CYMAKE) -o $(CYMAKE)


# Compile the frontend API
.PHONY: frontend

frontend:
	$(HC) -c $(FRONTEND_HS)


# Install the compiler
.PHONY: install


install: $(CYMAKE)
	@mv ./$(CYMAKE) $(MCC_BIN)/
