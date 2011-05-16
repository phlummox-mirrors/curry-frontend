> {-# LANGUAGE DeriveDataTypeable #-}

% $Id: CurrySyntax.lhs,v 1.43 2004/02/15 22:10:31 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{CurrySyntax.lhs}
\section{The Parse Tree}
This module provides the necessary data structures to maintain the
parsed representation of a Curry program.

\em{Note:} this modified version uses haskell type \texttt{Integer}
instead of \texttt{Int} for representing integer values. This allows
an unlimited range of integer constants in Curry programs.
\begin{verbatim}

> module Curry.Syntax.Type
>   ( -- * Data types
>     Module (..), ExportSpec (..), Export (..), ImportSpec (..), Import (..)
>   , Decl (..), ConstrDecl (..), NewConstrDecl (..), Qualified, Infix (..)
>   , EvalAnnotation (..), CallConv (..), Interface (..), IDecl (..)
>   , TypeExpr (..), Equation (..), Lhs (..), Rhs (..), CondExpr (..)
>   , Literal (..), ConstrTerm (..), Expression (..), InfixOp (..)
>   , Statement (..), Alt (..), Field (..)

>     -- * Functions
>   , flatLhs, mk', mk, mkInt, fieldLabel, fieldTerm, field2Tuple, opName
>   , addSrcRefs
>   ) where

> import Control.Monad.State
> import Data.Generics
> import qualified Data.Set as Set (fromList, notMember)

> import Curry.Base.Expr
> import Curry.Base.Ident
> import Curry.Base.Position

\end{verbatim}
\paragraph{Modules}
\begin{verbatim}

> data Module = Module [Pragma] ModuleIdent (Maybe ExportSpec) [Decl]
>               deriving (Eq,Show,Read,Typeable,Data)

> data Pragma = Pragma String String

> data ExportSpec = Exporting Position [Export]
>                   deriving (Eq,Show,Read,Typeable,Data)
> data Export
>   = Export         QualIdent                  -- f/T
>   | ExportTypeWith QualIdent [Ident]          -- T(C1,...,Cn)
>   | ExportTypeAll  QualIdent                  -- T(..)
>   | ExportModule   ModuleIdent
>     deriving (Eq,Show,Read,Typeable,Data)

\end{verbatim}
\paragraph{Module declarations}
\begin{verbatim}

> data ImportSpec
>   = Importing Position [Import]
>   | Hiding Position [Import]
>     deriving (Eq,Show,Read,Typeable,Data)
> data Import
>   = Import         Ident            -- f/T
>   | ImportTypeWith Ident [Ident]    -- T(C1,...,Cn)
>   | ImportTypeAll  Ident            -- T(..)
>     deriving (Eq,Show,Read,Typeable,Data)

> data Decl
>   = ImportDecl Position ModuleIdent Qualified (Maybe ModuleIdent)
>                (Maybe ImportSpec)
>   | InfixDecl Position Infix Integer [Ident]
>   | DataDecl Position Ident [Ident] [ConstrDecl]
>   | NewtypeDecl Position Ident [Ident] NewConstrDecl
>   | TypeDecl Position Ident [Ident] TypeExpr
>   | TypeSig Position [Ident] TypeExpr
>   | EvalAnnot Position [Ident] EvalAnnotation
>   | FunctionDecl Position Ident [Equation]
>   | ExternalDecl Position CallConv (Maybe String) Ident TypeExpr
>   | FlatExternalDecl Position [Ident]
>   | PatternDecl Position ConstrTerm Rhs
>   | ExtraVariables Position [Ident]
>     deriving (Eq,Show,Read,Typeable,Data)

> data ConstrDecl
>   = ConstrDecl Position [Ident] Ident [TypeExpr]
>   | ConOpDecl Position [Ident] TypeExpr Ident TypeExpr
>     deriving (Eq,Show,Read,Typeable,Data)

> data NewConstrDecl = NewConstrDecl Position [Ident] Ident TypeExpr
>                      deriving (Eq,Show,Read,Typeable,Data)

> type Qualified = Bool

> data Infix = InfixL | InfixR | Infix deriving (Eq,Show,Read,Typeable,Data)

> data EvalAnnotation = EvalRigid | EvalChoice
>                       deriving (Eq,Show,Read,Typeable,Data)

> data CallConv = CallConvPrimitive | CallConvCCall
>                 deriving (Eq,Show,Read,Typeable,Data)

\end{verbatim}
\paragraph{Module interfaces}
Interface declarations are restricted to type declarations and signatures.
Note that an interface function declaration additionaly contains the
function arity (= number of parameters) in order to generate
correct FlatCurry function applications.
\begin{verbatim}

> data Interface = Interface ModuleIdent [IDecl]
>                  deriving (Eq,Show,Read,Typeable,Data)

> data IDecl
>   = IImportDecl Position ModuleIdent
>   | IInfixDecl Position Infix Integer QualIdent
>   | HidingDataDecl Position Ident [Ident]
>   | IDataDecl Position QualIdent [Ident] [Maybe ConstrDecl]
>   | INewtypeDecl Position QualIdent [Ident] NewConstrDecl
>   | ITypeDecl Position QualIdent [Ident] TypeExpr
>   | IFunctionDecl Position QualIdent Int TypeExpr
>     deriving (Eq,Show,Read,Typeable,Data)

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> data TypeExpr
>   = ConstructorType QualIdent [TypeExpr]
>   | VariableType Ident
>   | TupleType [TypeExpr]
>   | ListType TypeExpr
>   | ArrowType TypeExpr TypeExpr
>   | RecordType [([Ident],TypeExpr)] (Maybe TypeExpr)
>     -- {l1 :: t1,...,ln :: tn | r}
>     deriving (Eq,Show,Read,Typeable,Data)

\end{verbatim}
\paragraph{Functions}
\begin{verbatim}

> data Equation = Equation Position Lhs Rhs
>                 deriving (Eq,Show,Read,Typeable,Data)

> data Lhs
>   = FunLhs Ident [ConstrTerm]
>   | OpLhs ConstrTerm Ident ConstrTerm
>   | ApLhs Lhs [ConstrTerm]
>     deriving (Eq,Show,Read,Typeable,Data)

> data Rhs
>   = SimpleRhs Position Expression [Decl]
>   | GuardedRhs [CondExpr] [Decl]
>     deriving (Eq,Show,Read,Typeable,Data)

> data CondExpr = CondExpr Position Expression Expression
>                 deriving (Eq,Show,Read,Typeable,Data)

> flatLhs :: Lhs -> (Ident,[ConstrTerm])
> flatLhs lhs = flat lhs []
>   where flat (FunLhs f ts)    ts' = (f, ts ++ ts')
>         flat (OpLhs t1 op t2) ts' = (op, t1:t2:ts')
>         flat (ApLhs lhs' ts)  ts' = flat lhs' (ts ++ ts')

\end{verbatim}
\paragraph{Literals} The \texttt{Ident} argument of an \texttt{Int}
literal is used for supporting ad-hoc polymorphism on integer
numbers. An integer literal can be used either as an integer number or
as a floating-point number depending on its context. The compiler uses
the identifier of the \texttt{Int} literal for maintaining its type.
\begin{verbatim}

> data Literal
>   = Char SrcRef Char        -- should be Int to handle Unicode
>   | Int Ident Integer
>   | Float SrcRef Double
>   | String SrcRef String    -- should be [Int] to handle Unicode
>     deriving (Eq,Show,Read,Typeable,Data)

> mk' :: ([SrcRef] -> a) -> a
> mk' = ($[])

> mk :: (SrcRef -> a) -> a
> mk = ($noRef)

> mkInt :: Integer -> Literal
> mkInt i = mk (\r -> Int (addPositionIdent (AST  r) anonId) i)

\end{verbatim}
\paragraph{Patterns}
\begin{verbatim}

> data ConstrTerm
>   = LiteralPattern Literal
>   | NegativePattern Ident Literal
>   | VariablePattern Ident
>   | ConstructorPattern QualIdent [ConstrTerm]
>   | InfixPattern ConstrTerm QualIdent ConstrTerm
>   | ParenPattern ConstrTerm
>   | TuplePattern SrcRef [ConstrTerm]
>   | ListPattern [SrcRef] [ConstrTerm]
>   | AsPattern Ident ConstrTerm
>   | LazyPattern SrcRef ConstrTerm
>   | FunctionPattern QualIdent [ConstrTerm]
>   | InfixFuncPattern ConstrTerm QualIdent ConstrTerm
>   | RecordPattern [Field ConstrTerm] (Maybe ConstrTerm)
>         -- {l1 = p1, ..., ln = pn}  oder {l1 = p1, ..., ln = pn | p}
>     deriving (Eq,Show,Read,Typeable,Data)

\end{verbatim}
\paragraph{Expressions}
\begin{verbatim}

> data Expression
>   = Literal Literal
>   | Variable QualIdent
>   | Constructor QualIdent
>   | Paren Expression
>   | Typed Expression TypeExpr
>   | Tuple SrcRef [Expression]
>   | List [SrcRef] [Expression]
>   | ListCompr SrcRef Expression [Statement] -- the ref corresponds to the main list
>   | EnumFrom Expression
>   | EnumFromThen Expression Expression
>   | EnumFromTo Expression Expression
>   | EnumFromThenTo Expression Expression Expression
>   | UnaryMinus Ident Expression
>   | Apply Expression Expression
>   | InfixApply Expression InfixOp Expression
>   | LeftSection Expression InfixOp
>   | RightSection InfixOp Expression
>   | Lambda SrcRef [ConstrTerm] Expression
>   | Let [Decl] Expression
>   | Do [Statement] Expression
>   | IfThenElse SrcRef Expression Expression Expression
>   | Case SrcRef Expression [Alt]
>   | RecordConstr [Field Expression]            -- {l1 = e1,...,ln = en}
>   | RecordSelection Expression Ident           -- e -> l
>   | RecordUpdate [Field Expression] Expression -- {l1 := e1,...,ln := en | e}
>     deriving (Eq,Show,Read,Typeable,Data)

> data InfixOp = InfixOp QualIdent | InfixConstr QualIdent
>                deriving (Eq,Show,Read,Typeable,Data)

> data Statement
>   = StmtExpr SrcRef Expression
>   | StmtDecl [Decl]
>   | StmtBind SrcRef ConstrTerm Expression
>     deriving (Eq,Show,Read,Typeable,Data)

> data Alt = Alt Position ConstrTerm Rhs deriving (Eq,Show,Read,Typeable,Data)

> data Field a = Field Position Ident a deriving (Eq, Show,Read,Typeable,Data)

> fieldLabel :: Field a -> Ident
> fieldLabel (Field _ l _) = l

> fieldTerm :: Field a -> a
> fieldTerm (Field _ _ t) = t

> field2Tuple :: Field a -> (Ident,a)
> field2Tuple (Field _ l t) = (l,t)

> opName :: InfixOp -> QualIdent
> opName (InfixOp op) = op
> opName (InfixConstr c) = c

\end{verbatim}

> instance SrcRefOf ConstrTerm where
>   srcRefOf (LiteralPattern l) = srcRefOf l
>   srcRefOf (NegativePattern i _) = srcRefOf i
>   srcRefOf (VariablePattern i) = srcRefOf i
>   srcRefOf (ConstructorPattern i _) = srcRefOf i
>   srcRefOf (InfixPattern _ i _) = srcRefOf i
>   srcRefOf (ParenPattern c) = srcRefOf c
>   srcRefOf (TuplePattern s _) = s
>   srcRefOf (ListPattern _ _) = error "list pattern has several source refs"
>   srcRefOf (AsPattern i _) = srcRefOf i
>   srcRefOf (LazyPattern s _) = s
>   srcRefOf (FunctionPattern i _) = srcRefOf i
>   srcRefOf (InfixFuncPattern _ i _) = srcRefOf i
>   srcRefOf (RecordPattern _ _) = undefined -- TODO ask Bernd for the implementation

> instance SrcRefOf Literal where
>   srcRefOf (Char s _)   = s
>   srcRefOf (Int i _)    = srcRefOf i
>   srcRefOf (Float s _)  = s
>   srcRefOf (String s _) = s

---------------------------
-- add source references
---------------------------

> type M a = a -> State Int a
>
> addSrcRefs :: Module -> Module
> addSrcRefs x = evalState (addRef' x) 0
>   where
>     addRef' :: Data a' => M a'
>     addRef' = down `extM` addRefPos
>                    `extM` addRefSrc
>                    `extM` addRefIdent
>                    `extM` addRefListPat
>                    `extM` addRefListExp
>       where
>         down :: Data a' => M a'
>         down = gmapM addRef'
>
>         addRefPos :: M [SrcRef]
>         addRefPos _ = liftM (:[]) nextRef
>
>         addRefSrc :: M SrcRef
>         addRefSrc _ = nextRef
>
>         addRefIdent :: M Ident
>         addRefIdent ident = liftM (flip addRefId ident) nextRef
>
>         addRefListPat :: M ConstrTerm
>         addRefListPat (ListPattern _ ts) = do
>           liftM (uncurry ListPattern) (addRefList ts)
>         addRefListPat ct = gmapM addRef' ct
>
>         addRefListExp :: M Expression
>         addRefListExp (List _ ts) = do
>           liftM (uncurry List) (addRefList ts)
>         addRefListExp ct = gmapM addRef' ct
>
>         addRefList :: Data a' => [a'] -> State Int ([SrcRef],[a'])
>         addRefList ts = do
>           i <- nextRef
>           let add t = do t' <- addRef' t;j <- nextRef; return (j,t')
>           ists <- sequence (map add ts)
>           let (is,ts') = unzip ists
>           return (i:is,ts')
>
>         nextRef :: State Int SrcRef
>         nextRef = do
>           i <- get
>           put $! i+1
>           return (SrcRef [i])

The \texttt{Decl} instance of \texttt{QualExpr} returns all free
variables on the right hand side, regardless of whether they are bound
on the left hand side. This is more convenient as declarations are
usually processed in a declaration group where the set of free
variables cannot be computed independently for each declaration. Also
note that the operator in a unary minus expression is not a free
variable. This operator always refers to a global function from the
prelude.

> instance QualExpr Decl where
>   qfv m (FunctionDecl _ _ eqs) = qfv m eqs
>   qfv m (PatternDecl _ _ rhs) = qfv m rhs
>   qfv _ _ = []

> instance QuantExpr Decl where
>   bv (TypeSig _ vs _) = vs
>   bv (EvalAnnot _ fs _) = fs
>   bv (FunctionDecl _ f _) = [f]
>   bv (ExternalDecl _ _ _ f _) = [f]
>   bv (FlatExternalDecl _ fs) = fs
>   bv (PatternDecl _ t _) = bv t
>   bv (ExtraVariables _ vs) = vs
>   bv _ = []

> instance QualExpr Equation where
>   qfv m (Equation _ lhs rhs) = filterBv lhs (qfv m lhs ++ qfv m rhs)

> instance QuantExpr Lhs where
>   bv = bv . snd . flatLhs

> instance QualExpr Lhs where
>   qfv m lhs = qfv m (snd (flatLhs lhs))

> instance QualExpr Rhs where
>   qfv m (SimpleRhs _ e ds) = filterBv ds (qfv m e ++ qfv m ds)
>   qfv m (GuardedRhs es ds) = filterBv ds (qfv m es ++ qfv m ds)

> instance QualExpr CondExpr where
>   qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

> instance QualExpr Expression where
>   qfv _ (Literal _) = []
>   qfv m (Variable v) = maybe [] return (localIdent m v)
>   qfv _ (Constructor _) = []
>   qfv m (Paren e) = qfv m e
>   qfv m (Typed e _) = qfv m e
>   qfv m (Tuple _ es) = qfv m es
>   qfv m (List _ es) = qfv m es
>   qfv m (ListCompr _ e qs) = foldr (qfvStmt m) (qfv m e) qs
>   qfv m (EnumFrom e) = qfv m e
>   qfv m (EnumFromThen e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromTo e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (UnaryMinus _ e) = qfv m e
>   qfv m (Apply e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (InfixApply e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
>   qfv m (LeftSection e op) = qfv m op ++ qfv m e
>   qfv m (RightSection op e) = qfv m op ++ qfv m e
>   qfv m (Lambda _ ts e) = filterBv ts (qfv m e)
>   qfv m (Let ds e) = filterBv ds (qfv m ds ++ qfv m e)
>   qfv m (Do sts e) = foldr (qfvStmt m) (qfv m e) sts
>   qfv m (IfThenElse _ e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (Case _ e alts) = qfv m e ++ qfv m alts
>   qfv m (RecordConstr fs) = qfv m fs
>   qfv m (RecordSelection e _) = qfv m e
>   qfv m (RecordUpdate fs e) = qfv m e ++ qfv m fs

> qfvStmt :: ModuleIdent -> Statement -> [Ident] -> [Ident]
> qfvStmt m st fvs = qfv m st ++ filterBv st fvs

> instance QualExpr Statement where
>   qfv m (StmtExpr _ e) = qfv m e
>   qfv m (StmtDecl ds) = filterBv ds (qfv m ds)
>   qfv m (StmtBind _ _ e) = qfv m e

> instance QualExpr Alt where
>   qfv m (Alt _ t rhs) = filterBv t (qfv m rhs)

> instance QuantExpr a => QuantExpr (Field a) where
>   bv (Field _ _ t) = bv t

> instance QualExpr a => QualExpr (Field a) where
>   qfv m (Field _ _ t) = qfv m t

> instance QuantExpr Statement where
>   bv (StmtExpr _ _) = []
>   bv (StmtBind _ t _) = bv t
>   bv (StmtDecl ds) = bv ds

> instance QualExpr InfixOp where
>   qfv m (InfixOp op) = qfv m (Variable op)
>   qfv _ (InfixConstr _) = []

> instance QuantExpr ConstrTerm where
>   bv (LiteralPattern _) = []
>   bv (NegativePattern _ _) = []
>   bv (VariablePattern v) = [v]
>   bv (ConstructorPattern _ ts) = bv ts
>   bv (InfixPattern t1 _ t2) = bv t1 ++ bv t2
>   bv (ParenPattern t) = bv t
>   bv (TuplePattern _ ts) = bv ts
>   bv (ListPattern _ ts) = bv ts
>   bv (AsPattern v t) = v : bv t
>   bv (LazyPattern _ t) = bv t
>   bv (FunctionPattern f ts) = bvFuncPatt (FunctionPattern f ts)
>   bv (InfixFuncPattern t1 op t2) = bvFuncPatt (InfixFuncPattern t1 op t2)
>   bv (RecordPattern fs r) = maybe [] bv r ++ bv fs

> instance QualExpr ConstrTerm where
>   qfv _ (LiteralPattern _) = []
>   qfv _ (NegativePattern _ _) = []
>   qfv _ (VariablePattern _) = []
>   qfv m (ConstructorPattern _ ts) = qfv m ts
>   qfv m (InfixPattern t1 _ t2) = qfv m [t1, t2]
>   qfv m (ParenPattern t) = qfv m t
>   qfv m (TuplePattern _ ts) = qfv m ts
>   qfv m (ListPattern _ ts) = qfv m ts
>   qfv m (AsPattern _ ts) = qfv m ts
>   qfv m (LazyPattern _ t) = qfv m t
>   qfv m (FunctionPattern f ts)
>     = maybe [] return (localIdent m f) ++ qfv m ts
>   qfv m (InfixFuncPattern t1 op t2)
>     = maybe [] return (localIdent m op) ++ qfv m [t1, t2]
>   qfv m (RecordPattern fs r) = maybe [] (qfv m) r ++ qfv m fs

> instance Expr TypeExpr where
>   fv (ConstructorType _ tys) = fv tys
>   fv (VariableType tv)
>     | tv == anonId = []
>     | otherwise = [tv]
>   fv (TupleType tys) = fv tys
>   fv (ListType ty) = fv ty
>   fv (ArrowType ty1 ty2) = fv ty1 ++ fv ty2
>   fv (RecordType fs rty) = maybe [] fv rty ++ fv (map snd fs)

> filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
> filterBv e = filter (`Set.notMember` Set.fromList (bv e))

Since multiple variable occurrences are allowed in function patterns,
it is necessary to compute the list of bound variables in a different way:
Each variable occuring in the function pattern will be unique in the result
list.

> bvFuncPatt :: ConstrTerm -> [Ident]
> bvFuncPatt = bvfp []
>  where
>  bvfp bvs (LiteralPattern _) = bvs
>  bvfp bvs (NegativePattern _ _) = bvs
>  bvfp bvs (VariablePattern v)
>     | v `elem` bvs = bvs
>     | otherwise    = v : bvs
>  bvfp bvs (ConstructorPattern _ ts) = foldl bvfp bvs ts
>  bvfp bvs (InfixPattern t1 _ t2) = foldl bvfp bvs [t1, t2]
>  bvfp bvs (ParenPattern t) = bvfp bvs t
>  bvfp bvs (TuplePattern _ ts) = foldl bvfp bvs ts
>  bvfp bvs (ListPattern _ ts) = foldl bvfp bvs ts
>  bvfp bvs (AsPattern v t)
>     | v `elem` bvs = bvfp bvs t
>     | otherwise  = bvfp (v : bvs) t
>  bvfp bvs (LazyPattern _ t) = bvfp bvs t
>  bvfp bvs (FunctionPattern _ ts) = foldl bvfp bvs ts
>  bvfp bvs (InfixFuncPattern t1 _ t2) = foldl bvfp bvs [t1, t2]
>  bvfp bvs (RecordPattern fs r)
>     = foldl bvfp (maybe bvs (bvfp bvs) r) (map fieldTerm fs)
