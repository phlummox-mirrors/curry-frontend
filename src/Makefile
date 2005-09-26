
# necessary files for builing a modified version of the Muenster Curry Compiler
# which is used as PAKCS frontend

#MCC_SRC = AbstractCurry.hs CurrySyntax.lhs IL2FlatCurry.old.hs Options.lhs \
#          CurrySyntaxTools.lhs ILCompile.lhs PatchPrelude.hs Arity.hs      \
#          IL.lhs PathUtils.lhs Base.lhs ILLift.lhs Position.lhs Cam.lhs    \
#          ILPP.lhs PrecCheck.lhs CamPP.lhs ILScope.hs Pretty.lhs           \
#          CaseCompletion.hs Desugar.lhs ILTrans.lhs Qual.lhs               \
#          DTransform.lhs ILxml.lhs SCC.lhs CCode.lhs Env.lhs Imports.lhs   \
#          ScopeEnv.hs CElim.lhs Error.lhs Set.lhs CGen.lhs Eval.lhs        \
#          Simplify.lhs Combined.lhs Exports.lhs KindCheck.lhs FlatCurry.hs \
#          LexComb.lhs Subst.lhs CPretty.lhs FlatCurry.lhs Lift.lhs         \
#          SyntaxCheck.lhs CPS.lhs LLParseComb.lhs TopEnv.lhs CurryDeps.lhs \
#          FlatInfo.lhs Map.lhs TypeCheck.lhs CurryInfo.hs                  \
#          GenAbstractCurry.hs Types.lhs CurryLexer.lhs GetOpt.hs           \
#          Modules.lhs TypeSubst.lhs Typing.lhs CurryParser.lhs Ident.lhs   \
#          NestEnv.lhs Unlit.lhs CurryPP.lhs IL2FlatCurry.hs Utils.lhs      \

MCC_SRC = AbstractCurry.hs Cam.lhs CCode.lhs Pretty.lhs CPretty.lhs CamPP.lhs  \
	  FlatCurry.hs Utils.lhs Position.lhs Unlit.lhs Error.lhs LexComb.lhs  \
	  Combined.lhs Ident.lhs CurrySyntax.lhs CurryPP.lhs Types.lhs IL.lhs  \
	  ILPP.lhs DTransform.lhs ILLift.lhs Map.lhs Set.lhs SCC.lhs CElim.lhs \
	  CPS.lhs CurryLexer.lhs LLParseComb.lhs CurryParser.lhs Subst.lhs     \
	  CGen.lhs Env.lhs TopEnv.lhs Base.lhs TypeSubst.lhs Typing.lhs        \
	  Desugar.lhs Qual.lhs Exports.lhs Arity.hs KindCheck.lhs ScopeEnv.hs  \
	  ILScope.hs CaseCompletion.hs ILCompile.lhs GenAbstractCurry.hs       \
	  CurryInfo.hs ILTrans.lhs ILxml.lhs Lift.lhs Simplify.lhs Eval.lhs    \
	  Imports.lhs TypeCheck.lhs PrecCheck.lhs NestEnv.lhs SyntaxCheck.lhs  \
	  GetOpt.hs Options.lhs CurryCompilerOpts.hs CurryBuilderOpts.hs       \
	  PathUtils.lhs CurryDeps.lhs PatchPrelude.hs IL2FlatCurry.hs          \
	  Modules.lhs CurryCompiler.hs CurryBuilder.hs Variables.hs

#CYCC_SRC   = cycc.hs
#CYCC       = cycc

#CYMK_SRC   = cymk.hs
#CYMK       = cymk

# a little program for updating target files depending on
# several source files (needed by cymake)
#SMAKE_SRC  = smake.hs
#SMAKE      = smake

# configuration file for generating script files "cyc" and "cymake"
#CONFIG_SRC = config.hs
#CONFIG     = config

# "cyc" and "cymake" samples
#CYC_PATT   = cyc-pattern
#CYC        = cyc

#CYMAKE_PATT= cymake-pattern
#CYMAKE     = cymake

# the command line compiler 'cymake'
CYMAKE_SRC = cymake.hs
CYMAKE     = cymake

# the haskell compiler
HC         = ghc
HC_OPTS	   = -syslib lang --make


# The following variables are exported by top level makefile
# MCC_PATH	- root path of the MCC

MCC_SRC = $(CURDIR)

# path to the MCC runtime source files
#MCC_SRC_RUNTIME	= $(MCC_SRC)/runtime

# path to the MCC library source files
#MCC_SRC_CURRY 	= $(MCC_SRC)/curry

# path to the mcc binaries
MCC_BIN  	= $(MCC_PATH)/bin

# path to the runtime libraries
#MCC_LIB_RUNTIME	= $(MCC_PATH)/lib/runtime


#------------------------------------------------------------------------------
# Let's start...


# Compile all MCC components
.PHONY: all

#all: src conf mcc runtime install
#all: src conf mcc install
all: src install

# Compile MCC components and generate "cycc", "cymk" and "smake"
.PHONY: src

src: $(CYMAKE)

$(CYMAKE): $(CYMAKE_SRC) $(MCC_SRC)
	$(HC) $(HC_OPTS) $(CYMAKE) -o $(CYMAKE)


#src: $(CYCC) $(SMAKE) $(CYMK)

#$(CYCC): $(MCC_SRC)
#	$(HC) $(HC_OPTS) $(CYCC) -o $(CYCC)

#$(SMAKE): $(SMAKE_SRC)
#	$(HC) $(HC_OPTS) $(SMAKE) -o $(SMAKE)

#$(CYMK): $(MCC_SRC) $(CYCC) $(SMAKE)
#	$(HC) $(HC_OPTS) $(CYMK) -o $(CYMK)


# Gnerate configuration program "config"
#.PHONY: conf

#conf: $(CONFIG)

#$(CONFIG): $(CONFIG_SRC)
#	$(HC) $(HC_OPTS) $(CONFIG) -o $(CONFIG)


# Generate "cyc" and "cymake"
#.PHONY: mcc

#mcc: $(CYC) $(CYMAKE)

#$(CYC): $(CYCC) $(CYC_PATT) $(CONFIG)
#	@./$(CONFIG) $(CYC)
#	@chmod 755 $(CYC)

#$(CYMAKE): $(CYMK) $(CYMAKE_PATT) $(CONFIG)
#	@./$(CONFIG) $(CYMAKE)
#	@chmod 755 $(CYMAKE)


# Generate the MCC runtime components
#.PHONY: runtime

#runtime:
#	echo Pos03
#	@cd $(MCC_SRC_RUNTIME) && make
#	echo Pos3


# Install the compiler
.PHONY: install

#install: inst_bin inst_rts

install: $(CYC) $(CYMAKE)
#	@cp ./$(CYC) $(MCC_BIN)/
	@cp ./$(CYMAKE) $(MCC_BIN)/

#inst_rts:
#	@cp ./$(SMAKE) $(MCC_LIB_RUNTIME)/
#	@cp ./$(CYCC) $(MCC_LIB_RUNTIME)/
#	@cp ./$(CYMK) $(MCC_LIB_RUNTIME)/

