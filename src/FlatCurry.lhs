------------------------------------------------------------------------------
--- Library to support meta-programming in Curry.
---
--- This library contains a definition for representing FlatCurry programs
--- in Haskell (type "Prog").
---
--- @author Michael Hanus
--- @version September 2003
---
--- @adapted to Haskell by Martin Engelke
--- @version December 2004
------------------------------------------------------------------------------

> module FlatCurry (Prog(..), QName, Visibility(..),
>                   TVarIndex, TypeDecl(..), ConsDecl(..), TypeExpr(..),
>                   OpDecl(..), Fixity(..),
>                   VarIndex, 
>                   FuncDecl(..), Rule(..), 
>                   CaseType(..), CombType(..), Expr(..), BranchExpr(..),
>                   Pattern(..), Literal(..)) where

import System 
import Directory
import Char
import ReadShowTerm
import PathUtils (doesModuleExist)

------------------------------------------------------------------------------
-- Definition of data types for representing FlatCurry programs:
-- =============================================================

--- Data type for representing a Curry module in the intermediate form.
--- A value of this data type has the form
--- <CODE>
---  (Prog modname imports typedecls functions opdecls translation_table)
--- </CODE>
--- where modname: name of this module,
---       imports: list of modules names that are imported,
---       typedecls, opdecls, functions, translation of type names
---       and constructor/function names: see below

> data Prog = Prog String [String] [TypeDecl] [FuncDecl] [OpDecl]


--- The data type for representing qualified names.
--- In FlatCurry all names are qualified to avoid name clashes.
--- The first component is the module name and the second component the
--- unqualified name as it occurs in the source program.

> type QName = (String,String)

--- Data type to specify the visibility of various entities.

> data Visibility = Public    -- public (exported) entity
>                 | Private   -- private entity

--- The data type for representing type variables.
--- They are represented by (TVar i) where i is a type variable index.

> type TVarIndex = Int

--- Data type for representing definitions of algebraic data types.
--- <PRE>
--- A data type definition of the form
---
--- data t x1...xn = ...| c t1....tkc |...
---
--- is represented by the FlatCurry term
---
--- (Type t [i1,...,in] [...(Cons c kc [t1,...,tkc])...])
---
--- where each ij is the index of the type variable xj
---
--- Note: the type variable indices are unique inside each type declaration
---       and are usually numbered from 0
---
--- Thus, a data type declaration consists of the name of the data type,
--- a list of type parameters and a list of constructor declarations.
--- </PRE>

> data TypeDecl = Type    QName Visibility [TVarIndex] [ConsDecl]
>               | TypeSyn QName Visibility [TVarIndex] TypeExpr

--- A constructor declaration consists of the name and arity of the
--- constructor and a list of the argument types of the constructor.

> data ConsDecl = Cons QName Int Visibility [TypeExpr]


--- Data type for type expressions.
--- A type expression is either a type variable, a function type,
--- or a type constructor application.
---
--- Note: the names of the predefined type constructors are
---       "Int", "Float", "Bool", "Char", "IO", "Success",
---       "()" (unit type), "(,...,)" (tuple types), "[]" (list type)

> data TypeExpr =
>      TVar TVarIndex                 -- type variable
>    | FuncType TypeExpr TypeExpr     -- function type t1->t2
>    | TCons QName [TypeExpr]         -- type constructor application
>                                     -- TCons module name typeargs


--- Data type for operator declarations.
--- An operator declaration "fix p n" in Curry corresponds to the
--- FlatCurry term (Op n fix p).

> data OpDecl = Op QName Fixity Int

--- Data types for the different choices for the fixity of an operator.

> data Fixity = InfixOp | InfixlOp | InfixrOp


--- Data type for representing object variables.
--- Object variables occurring in expressions are represented by (Var i)
--- where i is a variable index.

> type VarIndex = Int


--- Data type for representing function declarations.
--- <PRE>
--- A function declaration in FlatCurry is a term of the form
---
---  (Func name arity type (Rule [i_1,...,i_arity] e))
---
--- and represents the function "name" with definition
---
---   name :: type
---   name x_1...x_arity = e
---
--- where each i_j is the index of the variable x_j
---
--- Note: the variable indices are unique inside each function declaration
---       and are usually numbered from 0
---
--- External functions are represented as (Func name arity type (External s))
--- where s is the external name associated to this function.
---
--- Thus, a function declaration consists of the name, arity, type, and rule.
--- </PRE>

> data FuncDecl = Func QName Int Visibility TypeExpr Rule


--- A rule is either a list of formal parameters together with an expression
--- or an "External" tag.

> data Rule = Rule [VarIndex] Expr
>           | External String

--- Data type for classifying case expressions.
--- Case expressions can be either flexible or rigid in Curry.

> data CaseType = Rigid | Flex       -- type of a case expression

--- Data type for classifying combinations
--- (i.e., a function/constructor applied to some arguments).
--- @cons FuncCall - a call to a function where all arguments are provided
--- @cons PartCall - a partial call to a function (i.e., not all arguments
---                  are provided) where the parameter is the number of
---                  missing arguments
--- @cons ConsCall - a call with a constructor at the top (where it is
---                  possible that not all arguments are provided)

> data CombType = FuncCall | PartCall Int | ConsCall    

--- Data type for representing expressions.
---
--- Remarks:
--- <PRE>
--- 1. if-then-else expressions are represented as function calls:
---      (if e1 then e2 else e3)
---    is represented as
---      (Comb FuncCall ("Prelude","if_then_else") [e1,e2,e3])
--- 
--- 2. Higher order applications are represented as calls to the (external)
---    function "apply". For instance, the rule
---      app f x = f x
---    is represented as
---      (Rule  [0,1] (Comb FuncCall ("Prelude","apply") [Var 0, Var 1]))
--- 
--- 3. A conditional rule is represented as a call to an external function
---    "cond" where the first argument is the condition (a constraint).
---    For instance, the rule
---      equal2 x | x=:=2 = success
---    is represented as
---      (Rule [0]
---            (Comb FuncCall ("Prelude","cond")
---                  [Comb FuncCall ("Prelude","=:=") [Var 0, Lit (Intc 2)],
---                   Comb FuncCall ("Prelude","success") []]))
--- 
--- 4. Functions with evaluation annotation "choice" are represented
---    by a rule whose right-hand side is enclosed in a call to the
---    external function "Prelude.commit".
---    Furthermore, all rules of the original definition must be
---    represented by conditional expressions (i.e., (cond [c,e]))
---    after pattern matching.
---    Example:
--- 
---       m eval choice
---       m [] y = y
---       m x [] = x
--- 
---    is translated into (note that the conditional branches can be also
---    wrapped with Free declarations in general):
--- 
---       Rule [0,1]
---            (Comb FuncCall ("Prelude","commit")
---              [Or (Case Rigid (Var 0)
---                     [(Pattern ("Prelude","[]") []
---                         (Comb FuncCall ("Prelude","cond")
---                               [Comb FuncCall ("Prelude","success") [],
---                                Var 1]))] )
---                  (Case Rigid (Var 1)
---                     [(Pattern ("Prelude","[]") []
---                         (Comb FuncCall ("Prelude","cond")
---                               [Comb FuncCall ("Prelude","success") [],
---                                Var 0]))] )])
--- 
---    Operational meaning of (Prelude.commit e):
---    evaluate e with local search spaces and commit to the first
---    (Comb FuncCall ("Prelude","cond") [c,ge]) in e whose constraint c
---    is satisfied
--- </PRE>
--- @cons Var - variable (represented by unique index)
--- @cons Lit - literal (Integer/Float/Char constant)
--- @cons Comb - application (f e1 ... en) of function/constructor f
---              with n<=arity(f)
--- @cons Free - introduction of free local variables
--- @cons Or - disjunction of two expressions (used to translate rules
---            with overlapping left-hand sides)
--- @cons Case - case distinction (rigid or flex)

> data Expr = Var VarIndex 
>           | Lit Literal
>           | Comb CombType QName [Expr]
>           | Free [VarIndex] Expr
>           | Or Expr Expr
>           | Case CaseType Expr [BranchExpr]


--- Data type for representing branches in a case expression.
--- <PRE>
--- Branches "(m.c x1...xn) -> e" in case expressions are represented as
---
---   (Branch (Pattern (m,c) [i1,...,in]) e)
---
--- where each ij is the index of the pattern variable xj, or as
---
---   (Branch (LPattern (Intc i)) e)
---
--- for integers as branch patterns (similarly for other literals
--- like float or character constants).
--- </PRE>

> data BranchExpr = Branch Pattern Expr

--- Data type for representing patterns in case expressions.

> data Pattern = Pattern QName [VarIndex]
>              | LPattern Literal

--- Data type for representing literals occurring in an expression
--- or case branch. It is either an integer, a float, or a character constant.

> data Literal = Intc   Int
>              | Floatc Float
>              | Charc  Char


------------------------------------------------------------------------------
--- I/O action which parses a Curry program and returns the corresponding
--- FlatCurry program.
--- Thus, the argument is the file name without suffix ".curry"
--- (or ".lcurry") and the result is a FlatCurry term representing this
--- program.

readFlatCurry :: String -> IO Prog
readFlatCurry progfile = readFlatCurryWithParseOptions progfile "-quiet"

--- I/O action which reads a FlatCurry program from a file
--- with respect to some parser options.
--- This I/O action is used by the standard action <CODE>readFlatCurry</CODE>.
--- It is currently predefined only in Curry2Prolog.
--- @param progfile - the program file name (without suffix ".curry")
--- @param options - a string  with options passed to the PAKCS parser
---                  "parsecurry". Reasonable options are
---                  "-quiet -noprelude -nowarns" (or any subset of these).

readFlatCurryWithParseOptions :: String -> String -> IO Prog
readFlatCurryWithParseOptions progname options = do
  existsCurry <- doesModuleExist (progname++".curry")
  existsLCurry <- doesModuleExist (progname++".lcurry")
  if existsCurry || existsLCurry
   then do
     pakcshome <- getEnviron "PAKCSHOME"
     if null pakcshome
      then return 0
      else system (pakcshome++"/bin/parsecurry -fcy "++options++" "++progname)
   else return 0
  filename <- findFileInLoadPath (progname++".fcy")
  readFlatCurryFile filename

--- I/O action which reads a FlatCurry program from a file in ".fcy" format.
--- In contrast to <CODE>readFlatCurry</CODE>, this action does not parse
--- a source program. Thus, the argument must be the name of an existing
--- file (with suffix ".fcy") containing a FlatCurry program in ".fcy"
--- format and the result is a FlatCurry term representing this program.

readFlatCurryFile :: String -> IO Prog
readFlatCurryFile filename = readTermFile filename


--- I/O action which returns the interface of a Curry program, i.e.,
--- a FlatCurry program containing only "Public" entities and function
--- definitions without rules (i.e., external functions).
--- The argument is the file name without suffix ".curry"
--- (or ".lcurry") and the result is a FlatCurry term representing the
--- interface of this program.

readFlatCurryInt :: String -> IO Prog
readFlatCurryInt progname = do
  pakcshome <- getEnviron "PAKCSHOME"
  if null pakcshome
   then return 0
   else system (pakcshome++"/bin/parsecurry -fint "++progname)
  filename <- findFileInLoadPath (progname++".fint")
  readFlatCurryFile filename


--- Writes a FlatCurry program into a file in ".fcy" format.
--- The first argument must be the name of the target file
--- (with suffix ".fcy").
writeFCY :: String -> Prog -> IO ()
writeFCY file prog = writeTermFile file prog


-----------------------------------------------------------------------
--- Translates a given qualified type name into external name relative to
--- a module. Thus, names not defined in this module (except for names
--- defined in the prelude) are prefixed with their module name.
showQNameInModule :: String -> (String,String) -> String
showQNameInModule mod (qmod,name) =
  if qmod==mod || qmod=="Prelude"
  then name
  else qmod++"."++name

