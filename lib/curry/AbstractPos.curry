------------------------------------------------------------------------------
--- Library to support meta-programming in Curry.
---
--- This library contains a definition for representing Curry programs
--- in Curry (type "CurryProg") and an I/O action to read Curry programs and
--- transform them into this abstract representation (function "readCurry").
---
--- Note: this defines an extended format of AbstractCurry in comparison
--- to the version from april 2004.
---
--- Assumption: an abstract Curry program is stored in file prog.abstract.
---
--- @author Michael Hanus, Bernd Brassel, Martin Engelke
--- @version August 2005
------------------------------------------------------------------------------

module Abstract where

import System
import Directory
import ReadShowTerm


------------------------------------------------------------------------------
-- Definition of data types for representing abstract Curry programs:
-- ==================================================================

--- Data type for representing a Curry module in the intermediate form.
--- A value of this data type has the form
--- <CODE>
---  (CProg modname imports typedecls functions opdecls)
--- </CODE>
--- where modname: name of this module,
---       imports: list of modules names that are imported,
---       typedecls, opdecls, functions: see below

data CurryProg = CurryProg String [String] [CTypeDecl] [CFuncDecl] [COpDecl]


--- The data type for representing qualified names.
--- In AbstractCurry all names are qualified to avoid name clashes.
--- The first component is the module name and the second component the
--- unqualified name as it occurs in the source program.
type QName = (String,String)

--- The data type for representing identifiers for variable of any kind
--- (if possible, the identifier written in the source program).
type Name = String

--- The data type for representing positions of curry terms (e.g. declarations,
--- function rules etc.).
--- The first component is the line number and the second component is the
--- column number where the corresponding term occurs in the source program.
--- The position annotation is embeddet in a 'Maybe' term to allow an
--- easier handling of abstract curry programs (e.g. when generating
--- new declarations).
type Position = Maybe (Int, Int)


-- Data type to specify the visibility of various entities.

data CVisibility = CPublic    -- exported entity
                 | CPrivate   -- private entity


--- Data type for representing definitions of algebraic data types
--- and type synonyms.
--- <PRE>
--- A data type definition of the form
---
--- data t x1...xn = ...| c t1....tkc |...
---
--- is represented by the Curry term
---
--- (CType t v [i1,...,in] [...(CCons c kc v [t1,...,tkc])...])
---
--- where each ij is the indentifier of a type variable.
---
--- Thus, a data type declaration consists of the name of the data type,
--- a list of type parameters and a list of constructor declarations.
--- </PRE>

data CTypeDecl = CType    QName Position CVisibility [Name] [CConsDecl]
               | CTypeSyn QName Position CVisibility [Name] CTypeExpr


--- A constructor declaration consists of the name and arity of the
--- constructor and a list of the argument types of the constructor.

data CConsDecl = CCons QName Position Int CVisibility [CTypeExpr]


--- Data type for type expressions.
--- A type expression is either a type variable, a function type,
--- or a type constructor application.
---
--- Note: the names of the predefined type constructors are
---       "Int", "Float", "Bool", "Char", "IO", "Success",
---       "()" (unit type), "(,...,)" (tuple types), "[]" (list type)

data CTypeExpr =
    CTVar Name                     -- type variable
  | CFuncType CTypeExpr CTypeExpr  -- function type t1->t2
  | CTCons QName [CTypeExpr]       -- type constructor application
                                   -- (CTCons (module,name) arguments)


--- Data type for operator declarations.
--- An operator declaration "fix p n" in Curry corresponds to the
--- AbstractCurry term (COp n fix p).

data COpDecl = COp [QName] Position CFixity Int

data CFixity = CInfixOp   -- non-associative infix operator
             | CInfixlOp  -- left-associative infix operator
             | CInfixrOp  -- right-associative infix operator


--- Data type for representing function declarations.
--- <PRE>
--- A function declaration in FlatCurry is a term of the form
---
---  (CFunc name arity visibility type (CRules eval [CRule rule1,...,rulek]))
---
--- and represents the function "name" with definition
---
---   name :: type
---   rule1
---   ...
---   rulek
---
--- Note: the function type is embeddes in a 'Maybe' term to allow
---       representations of untyped function declarations
---
--- External functions are represented as (CFunc name arity type (CExternal s))
--- where s is the external name associated to this function.
---
--- Thus, a function declaration consists of the name, arity, type, and
--- a list of rules.
--- </PRE>

data CFuncDecl = CFunc QName Int CVisibility (Maybe TypeSig) CRules

data TypeSig = TypeSig Position CTypeExpr

--- A rule is either a list of formal parameters together with an expression
--- (i.e., a rule in flat form), a list of general program rules with
--- an evaluation annotation, or it is externally defined

data CRules = CRules CEvalAnnot [CRule]
            | CExternal Position String

--- Data type for classifying evaluation annotations for functions.
--- They can be either flexible (default), rigid, or choice.

data CEvalAnnot = CFlex | CRigid | CChoice

--- Data term for representing right-hand-sides (e.g. in function rules).
--- <PRE>
--- A right-hand-side can either be a simple expression or a guarded
--- exprssion of the form
---
---  (CGuardedExpr guard expr)
---
--- where "guard" is an expression of type 'Bool' or 'Success'.
---
--- Note: a simple expression is (semantically) equivalent to the corresponding
---       guarded expression with the guard "success".
--- </PRE>
data CRhs = CSimpleExpr Position CExpr | CGuardedExpr [(Position,CExpr,CExpr)]

--- The most general form of a rule. It consists of a list of patterns
--- (left-hand side), a list of guards ("success" if not present in the
--- source text) with their corresponding right-hand sides, and
--- a list of local declarations.
data CRule = CRule [CPattern] CRhs [CLocalDecl]

--- Data type for representing local (let/where) declarations
data CLocalDecl =
     CLocalFunc CFuncDecl                            -- local function decl.
   | CLocalPat  CPattern CRhs [CLocalDecl]           -- local pattern decl.
   | CLocalVars Position [Name]                      -- local free variable 
                                                     -- declaration

--- Data type for representing Curry expressions.

data CExpr =
   CVar      Name                   -- variable (name)
 | CLit      CLiteral               -- literal (Integer/Float/Char constant)
 | CSymbol   QName                  -- a defined symbol with module and name
 | CApply    CExpr CExpr            -- application (e1 e2)
 | CLambda   [CPattern] CExpr       -- lambda abstraction
 | CLetDecl  [CLocalDecl] CExpr     -- local let declarations
 | CDoExpr   [CStatement]           -- do expression
 | CListComp CExpr [CStatement]     -- list comprehension
 | CCase     CExpr [CBranchExpr]    -- case expression

--- Data type for representing statements in do expressions and
--- list comprehensions.

data CStatement = CSExpr CExpr         -- an expression (I/O action or boolean)
                | CSPat CPattern CExpr -- a pattern definition
                | CSLet [CLocalDecl]   -- a local let declaration

--- Data type for representing pattern expressions.

data CPattern =
   CPVar Name              -- pattern variable (name)
 | CPLit CLiteral          -- literal (Integer/Float/Char constant)
 | CPComb QName [CPattern] -- application (m.c e1 ... en) of n-ary
                           -- constructor m.c (CPComb (m,c) [e1,...,en])

--- Data type for representing branches in case expressions.

data CBranchExpr = CBranch CPattern CRhs

--- Data type for representing literals occurring in an expression.
--- It is either an integer, a float, or a character constant.

data CLiteral = CIntc   Int
              | CFloatc Float
              | CCharc  Char

------------------------------------------------------------------------------
{-
--- I/O action which parses a Curry program and returns the corresponding
--- typed Abstract Curry program.
--- Thus, the argument is the file name without suffix ".curry"
--- or ".lcurry") and the result is a Curry term representing this
--- program.

readCurry :: String -> IO CurryProg
readCurry prog = readCurryWithParseOptions prog "-quiet"

--- I/O action which parses a Curry program and returns the corresponding
--- untyped Abstract Curry program.
--- Thus, the argument is the file name without suffix ".curry"
--- or ".lcurry") and the result is a Curry term representing this
--- program.

readUntypedCurry :: String -> IO CurryProg
readUntypedCurry prog = readUntypedCurryWithParseOptions prog "-quiet"

--- I/O action which reads a typed Curry program from a file (with extension
--- ".acy") with respect to some parser options.
--- This I/O action is used by the standard action <CODE>readCurry</CODE>.
--- It is currently predefined only in Curry2Prolog.
--- @param progfile - the program file name (without suffix ".curry")
--- @param options - a string  with options passed to the PAKCS parser
---                  "parsecurry". Reasonable options are
---                  "-quiet -noprelude -nowarns" (or any subset of these).

readCurryWithParseOptions :: String -> String -> IO CurryProg
readCurryWithParseOptions progname options = do
  existsCurry <- doesFileExist (progname++".curry")
  existsLCurry <- doesFileExist (progname++".lcurry")
  if existsCurry || existsLCurry
   then do
     pakcshome <- getEnviron "PAKCSHOME"
     if null pakcshome
      then return 0
      else system (pakcshome++"/bin/parsecurry -acy "++options++" "++progname)
   else return 0
  filename <- findFileInLoadPath (progname++".acy")
  readAbstractCurryFile filename

--- I/O action which reads an untyped Curry program from a file (with extension
--- ".uacy") with respect to some parser options. For more details
--- see function 'readCurryWithParseOptions'
readUntypedCurryWithParseOptions :: String -> String -> IO CurryProg
readUntypedCurryWithParseOptions progname options = do
  existsCurry <- doesFileExist (progname++".curry")
  existsLCurry <- doesFileExist (progname++".lcurry")
  if existsCurry || existsLCurry
   then do
     pakcshome <- getEnviron "PAKCSHOME"
     if null pakcshome
      then return 0
      else system (pakcshome++"/bin/parsecurry -uacy "++options++" "++progname)
   else return 0
  filename <- findFileInLoadPath (progname++".uacy")
  readAbstractCurryFile filename

--- I/O action which reads an AbstractCurry program from a file in ".acy"
--- format. In contrast to <CODE>readCurry</CODE>, this action does not parse
--- a source program. Thus, the argument must be the name of an existing
--- file (with suffix ".acy") containing an AbstractCurry program in ".acy"
--- format and the result is a Curry term representing this program.
--- It is currently predefined only in Curry2Prolog.

readAbstractCurryFile :: String -> IO CurryProg
readAbstractCurryFile filename = do
  filecontents <- readFile filename
  return (readUnqualifiedTerm ["AbstractCurry","prelude"] filecontents)


--- Writes an AbstractCurry program into a file in ".acy" format.
--- The first argument must be the name of the target file
--- (with suffix ".acy").
writeAbstractCurryFile :: String -> CurryProg -> IO ()
writeAbstractCurryFile file prog = writeFile file (showTerm prog)
-}
------------------------------------------------------------------------------
