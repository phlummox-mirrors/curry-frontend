
# necessary files for builing a modified version of the Muenster Curry Compiler
# which is used as PAKCS frontend

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

# the command line compiler 'cymake'
CYMAKE_SRC = cymake.hs
CYMAKE     = cymake

# the haskell compiler
HC         = ghc
HC_OPTS	   = -syslib lang --make


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


# Compile MCC components and generate "cycc", "cymk" and "smake"
.PHONY: src

src: $(CYMAKE)

$(CYMAKE): $(CYMAKE_SRC) $(MCC_SRC)
	$(HC) $(HC_OPTS) $(CYMAKE) -o $(CYMAKE)


# Install the compiler
.PHONY: install


install: $(CYC) $(CYMAKE)
	@cp ./$(CYMAKE) $(MCC_BIN)/
