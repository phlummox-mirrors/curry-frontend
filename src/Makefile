
# necessary files for builing a simple version of the Muenster Curry Compiler
GETOPT_SRC = GetOpt.hs
MCC1_SRC   = Position.lhs Cam.lhs Map.lhs Set.lhs SCC.lhs CPS.lhs Ident.lhs  \
	     CurrySyntax.lhs Types.lhs Utils.lhs Subst.lhs Unlit.lhs IL.lhs  \
	     DTransform.lhs CCode.lhs CElim.lhs CGen.lhs                     \
	     Pretty.lhs ILPP.lhs CurryPP.lhs CPretty.lhs CamPP.lhs Error.lhs \
	     Combined.lhs ILLift.lhs LexComb.lhs CurryLexer.lhs              \
	     LLParseComb.lhs CurryParser.lhs Env.lhs ILCompile.lhs           \
	     TopEnv.lhs Base.lhs ILTrans.lhs Lift.lhs Qual.lhs               \
	     Eval.lhs Exports.lhs Imports.lhs IntfCheck.lhs PrecCheck.lhs    \
	     KindCheck.lhs TypeSubst.lhs Typing.lhs Simplify.lhs Desugar.lhs \
	     TypeCheck.lhs NestEnv.lhs SyntaxCheck.lhs PathUtils.lhs         \
	     Options.lhs CurryDeps.lhs
MCC2_SRC   = CaseCompletion.hs FlatCurry.hs           \
	     CurryInfo.hs IL2FlatCurry.hs
MCC3_SRC   = ILxml.lhs Modules.lhs

GETOPT_OBJ = GetOpt.o
MCC1_OBJ   = $(MCC1_SRC:%.lhs=%.o)
MCC2_OBJ   = $(MCC2_SRC:%.hs=%.o)
MCC3_OBJ   = $(MCC3_SRC:%.lhs=%.o)

CYCC_SRC   = cycc.hs
CYCC       = cycc
CYCC_OBJ   = cycc.o

CYMK_SRC   = cymk.hs
CYMK       = cymk
CYMK_OBJ   = cymk.o

# a little program needed by "cymake"
NEWER_LHS  = newer.lhs
NEWER      = newer

# configuration file for generating "cyc", "cymake" and "cyxml.hs"
CONFIG_SRC = config.hs
CONFIG     = config


CYC_PATT   = cyc-pattern
CYC        = cyc

CYMAKE_PATT= cymake-pattern
CYMAKE     = cymake

CYXML_HS_PATT = cyxml.hs-pattern
CYXML_HS      = cyxml.hs
CYXML         = cyxml

# the haskell compiler
HC         = ghc -syslib lang
HC_OPTS	   = -v0


# The following variables are exported by top level makefile
# MCC_PATH	- root path of the MCC

# path to the MCC runtime source files
MCC_SRC_RUNTIME	= $(MCC_PATH)/src/runtime

# path to the MCC library source files
MCC_SRC_CURRY 	= $(MCC_PATH)/src/curry

# path to the mcc binaries
MCC_BIN  	= $(MCC_PATH)/bin

# path to the runtime libraries
MCC_LIB_RUNTIME	= $(MCC_PATH)/lib/runtime


#------------------------------------------------------------------------------
# Let's start...


# Compile all MCC components
.PHONY: all

all: src conf mcc runtime install


# Compile MCC components and generate "cycc" and "cymk"
.PHONY: src

src: $(GETOPT_OBJ) $(MCC1_OBJ) $(MCC2_OBJ) $(MCC3_OBJ) $(CYCC) $(CYMK) $(NEWER)


$(GETOPT_OBJ): $(GETOPT_SRC)
	$(HC) $(HC_OPTS) -c $(GETOPT_SRC)

$(MCC1_OBJ): %.o: %.lhs $(GETOPT_OBJ)
	$(HC) $(HC_OPTS) -c $<

$(MCC2_OBJ): %.o: %.hs $(MCC1_OBJ) $(GETOPT_OBJ)
	$(HC) $(HC_OPTS) -c $<

$(MCC3_OBJ): %.o: %.lhs $(MCC2_OBJ) $(MCC1_OBJ) $(GETOPT_OBJ)
	$(HC) $(HC_OPTS) -c $<

$(CYCC): $(CYCC_SRC) $(MCC3_OBJ) $(MCC2_OBJ) $(MCC1_OBJ) $(GETOPT_OBJ)
	@rm $(CYCC_OBJ)
	$(HC) $(HC_OPTS) -o $(CYCC) $(CYCC_SRC) \
			    $(MCC3_OBJ) $(MCC2_OBJ) $(MCC1_OBJ) $(GETOPT_OBJ)

$(CYMK): $(CYMK_SRC) $(MCC3_OBJ) $(MCC2_OBJ) $(MCC1_OBJ) $(GETOPT_OBJ)
	@rm $(CYMK_OBJ)
	$(HC) $(HC_OPTS) -o $(CYMK) $(CYMK_SRC) \
			    $(MCC3_OBJ) $(MCC2_OBJ) $(MCC1_OBJ) $(GETOPT_OBJ)

$(NEWER): $(NEWER_LHS)
	$(HC) $(HC_OPTS) -o $(NEWER) $(NEWER_LHS)


# Compile configuration file "config.hs"
.PHONY: conf

conf: $(CONFIG)

$(CONFIG): $(CONFIG_SRC)
	$(HC) $(HC_OPTS) -o $(CONFIG) $(CONFIG_SRC)


# Generate "cyc", "cymake" and "cyxml"
.PHONY: mcc

mcc: $(CYC) $(CYMAKE) $(CYXML)

$(CYC): $(CONFIG) $(CYC_PATT)
	@./$(CONFIG) $(CYC)
	@chmod 755 $(CYC)
	@cd $(MCC_SRC_CURRY) && clean

$(CYMAKE): $(CONFIG) $(CYMAKE_PATT) $(NEWER)
	@./$(CONFIG) $(CYMAKE)
	@chmod 755 $(CYMAKE)

$(CYXML_HS): $(CYXML_HS_PATT)
	@./$(CONFIG) $(CYXML_HS)

$(CYXML): $(CYXML_HS) $(CYXML_HS_PATT) $(CYC) $(CYMAKE)
	$(HC) $(HC_OPTS) -o $(CYXML) $(CYXML_HS)


# Generate the MCC runtime components
.PHONY: runtime

runtime:
	@cd $(MCC_SRC_RUNTIME) && make


# Install the compiler
.PHONY: install

install: inst_bin inst_rts inst_lib

inst_bin: $(CYC) $(CYMAKE) $(CYXML)
	@cp ./$(CYC) $(MCC_BIN)/
	@cp ./$(CYMAKE) $(MCC_BIN)/
	@cp ./$(CYXML) $(MCC_BIN)/

inst_rts:
	@cp ./$(NEWER) $(MCC_LIB_RUNTIME)/
	@cp ./$(CYCC) $(MCC_LIB_RUNTIME)/
	@cp ./$(CYMK) $(MCC_LIB_RUNTIME)/

inst_lib: $(CYC) inst_rts
	@cd $(MCC_SRC_CURRY) && make
