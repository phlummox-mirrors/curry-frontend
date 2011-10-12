% $Id: Qual.lhs,v 1.18 2004/02/15 22:10:36 wlux Exp $
%
% Copyright (c) 2001-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% Modified by Björn Peemöller (bjp@informatik.uni-kiel.de)
%
\nwfilename{Qual.lhs}
\section{Proper Qualification}
After checking the module and before starting the translation into the
intermediate language, the compiler properly qualifies all type constructors,
data constructors and (global) functions occurring in a pattern or
expression such that their module prefix matches the module of their
definition. This is done also for functions and constructors declared
in the current module. Only functions and variables declared in local
declarations groups as well as function arguments remain unchanged.
\begin{verbatim}

> module Transformations.Qual (qual) where

> import Control.Monad (liftM, liftM2, liftM3)
> import qualified Control.Monad.Reader as R (Reader, asks, runReader)

> import Curry.Base.Ident
> import Curry.Syntax

> import Base.TopEnv

> import Env.TypeConstructors (TCEnv, qualLookupTC)
> import Env.Value (ValueEnv, qualLookupValue)

> data QualEnv = QualEnv
>   { moduleIdent :: ModuleIdent
>   , tyConsEnv   :: TCEnv
>   , valueEnv    :: ValueEnv
>   }

> type Qual a = a -> R.Reader QualEnv a

> qual :: ModuleIdent -> TCEnv -> ValueEnv -> [Decl] -> [Decl]
> qual m tcEnv tyEnv ds = R.runReader (mapM qualDecl ds)
>                                     (QualEnv m tcEnv tyEnv)

> qualDecl :: Qual Decl
> qualDecl i@(InfixDecl     _ _ _ _) = return i
> qualDecl (DataDecl      p n vs cs) =
>   DataDecl p n vs `liftM` mapM qualConstr cs
> qualDecl (NewtypeDecl   p n vs nc) =
>   NewtypeDecl p n vs `liftM` qualNewConstr nc
> qualDecl (TypeDecl      p n vs ty) = TypeDecl p n vs `liftM` qualTypeExpr ty
> qualDecl (TypeSig         p fs ty) = TypeSig p fs    `liftM` qualTypeExpr ty
> qualDecl e@(EvalAnnot       _ _ _) = return e
> qualDecl (FunctionDecl    p f eqs) =
>   FunctionDecl p f `liftM` mapM qualEqn eqs
> qualDecl (ExternalDecl p c x n ty) =
>   ExternalDecl p c x n `liftM` qualTypeExpr ty
> qualDecl fe@(FlatExternalDecl _ _) = return fe
> qualDecl (PatternDecl     p t rhs) =
>   liftM2 (PatternDecl p) (qualTerm t) (qualRhs rhs)
> qualDecl vs@(ExtraVariables   _ _) = return vs

> qualConstr :: Qual ConstrDecl
> qualConstr (ConstrDecl     p vs n tys) =
>   ConstrDecl p vs n `liftM` mapM qualTypeExpr tys
> qualConstr (ConOpDecl p vs ty1 op ty2) =
>   liftM2 (flip (ConOpDecl p vs) op) (qualTypeExpr ty1) (qualTypeExpr ty2)

> qualNewConstr :: Qual NewConstrDecl
> qualNewConstr (NewConstrDecl p vs n ty) =
>   NewConstrDecl p vs n `liftM` qualTypeExpr ty

> qualTypeExpr :: Qual TypeExpr
> qualTypeExpr (ConstructorType q tys) =
>   liftM2 ConstructorType (qualConstructor q) (mapM qualTypeExpr tys)
> qualTypeExpr v@(VariableType      _) = return v
> qualTypeExpr (TupleType         tys) =
>   TupleType `liftM` mapM qualTypeExpr tys
> qualTypeExpr (ListType           ty) = ListType `liftM` qualTypeExpr ty
> qualTypeExpr (ArrowType     ty1 ty2) =
>   liftM2 ArrowType (qualTypeExpr ty1) (qualTypeExpr ty2)
> qualTypeExpr (RecordType     fs rty) =
>   liftM2 RecordType (mapM qualFieldType fs) (qualRecordType rty)
>   where
>   qualFieldType (ls, ty) = do
>     ty' <- qualTypeExpr ty
>     return (ls, ty')
>   qualRecordType Nothing  = return Nothing
>   qualRecordType (Just v) = Just `liftM` qualTypeExpr v

> qualEqn :: Qual Equation
> qualEqn (Equation p lhs rhs) =
>   liftM2 (Equation p) (qualLhs lhs) (qualRhs rhs)

> qualLhs :: Qual Lhs
> qualLhs (FunLhs    f ts) = FunLhs f `liftM` mapM qualTerm ts
> qualLhs (OpLhs t1 op t2) =
>   liftM2 (flip OpLhs op) (qualTerm t1) (qualTerm t2)
> qualLhs (ApLhs   lhs ts) =
>   liftM2 ApLhs (qualLhs lhs) (mapM qualTerm ts)

> qualTerm :: Qual ConstrTerm
> qualTerm l@(LiteralPattern        _) = return l
> qualTerm n@(NegativePattern     _ _) = return n
> qualTerm v@(VariablePattern       _) = return v
> qualTerm (ConstructorPattern   c ts) =
>   liftM2 ConstructorPattern (qualIdent c) (mapM qualTerm ts)
> qualTerm (InfixPattern     t1 op t2) =
>   liftM3 InfixPattern (qualTerm t1) (qualIdent op) (qualTerm t2)
> qualTerm (ParenPattern            t) = ParenPattern `liftM` qualTerm t
> qualTerm (TuplePattern         p ts) =
>   TuplePattern p `liftM` mapM qualTerm ts
> qualTerm (ListPattern          p ts) =
>   ListPattern  p `liftM` mapM qualTerm ts
> qualTerm (AsPattern             v t) = AsPattern    v `liftM` qualTerm t
> qualTerm (LazyPattern           p t) = LazyPattern  p `liftM` qualTerm t
> qualTerm (FunctionPattern      f ts) =
>   liftM2 FunctionPattern (qualIdent f) (mapM qualTerm ts)
> qualTerm (InfixFuncPattern t1 op t2) =
>   liftM3 InfixFuncPattern (qualTerm t1) (qualIdent op) (qualTerm t2)
> qualTerm (RecordPattern       fs rt) =
>   liftM2 RecordPattern (mapM qualFieldPattern fs) (qualRecordTerm rt)
>   where qualRecordTerm Nothing  = return Nothing
>         qualRecordTerm (Just v) = Just `liftM` qualTerm v

> qualFieldPattern :: Qual (Field ConstrTerm)
> qualFieldPattern (Field p l t) = Field p l `liftM` qualTerm t

> qualRhs :: Qual Rhs
> qualRhs (SimpleRhs p e ds) =
>   liftM2 (SimpleRhs p) (qualExpr e) (mapM qualDecl ds)
> qualRhs (GuardedRhs es ds) =
>   liftM2 GuardedRhs (mapM qualCondExpr es) (mapM qualDecl ds)

> qualCondExpr :: Qual CondExpr
> qualCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (qualExpr g) (qualExpr e)

> qualExpr :: Qual Expression
> qualExpr l@(Literal             _) = return l
> qualExpr (Variable              v) = Variable `liftM` qualIdent v
> qualExpr (Constructor           c) = Constructor `liftM` qualIdent c
> qualExpr (Paren                 e) = Paren `liftM` qualExpr e
> qualExpr (Typed              e ty) =
>   liftM2 Typed (qualExpr e) (qualTypeExpr ty)
> qualExpr (Tuple              p es) = Tuple p `liftM` mapM qualExpr es
> qualExpr (List               p es) = List p `liftM` mapM qualExpr es
> qualExpr (ListCompr        p e qs) =
>   liftM2 (ListCompr p) (qualExpr e) (mapM qualStmt qs)
> qualExpr (EnumFrom              e) = EnumFrom `liftM` qualExpr e
> qualExpr (EnumFromThen      e1 e2) =
>   liftM2 EnumFromThen (qualExpr e1) (qualExpr e2)
> qualExpr (EnumFromTo        e1 e2) =
>   liftM2 EnumFromTo (qualExpr e1) (qualExpr e2)
> qualExpr (EnumFromThenTo e1 e2 e3) =
>   liftM3 EnumFromThenTo (qualExpr e1) (qualExpr e2) (qualExpr e3)
> qualExpr (UnaryMinus         op e) = UnaryMinus op `liftM` qualExpr e
> qualExpr (Apply             e1 e2) =
>   liftM2 Apply (qualExpr e1) (qualExpr e2)
> qualExpr (InfixApply     e1 op e2) =
>   liftM3 InfixApply (qualExpr e1) (qualOp op) (qualExpr e2)
> qualExpr (LeftSection        e op) =
>   liftM2 LeftSection (qualExpr e) (qualOp op)
> qualExpr (RightSection       op e) =
>   liftM2 RightSection (qualOp op) (qualExpr e)
> qualExpr (Lambda           r ts e) =
>   liftM2 (Lambda r) (mapM qualTerm ts) (qualExpr e)
> qualExpr (Let                ds e) =
>   liftM2 Let (mapM qualDecl ds) (qualExpr e)
> qualExpr (Do                sts e) =
>   liftM2 Do (mapM qualStmt sts) (qualExpr e)
> qualExpr (IfThenElse   r e1 e2 e3) =
>   liftM3 (IfThenElse r) (qualExpr e1) (qualExpr e2) (qualExpr e3)
> qualExpr (Case           r e alts) =
>   liftM2 (Case r) (qualExpr e) (mapM qualAlt alts)
> qualExpr (RecordConstr         fs) =
>   RecordConstr `liftM` mapM qualFieldExpr fs
> qualExpr (RecordSelection     e l) =
>   flip RecordSelection l `liftM` qualExpr e
> qualExpr (RecordUpdate       fs e) =
>   liftM2 RecordUpdate (mapM qualFieldExpr fs) (qualExpr e)

> qualStmt :: Qual Statement
> qualStmt (StmtExpr p   e) = StmtExpr p `liftM` qualExpr e
> qualStmt (StmtBind p t e) = liftM2 (StmtBind p) (qualTerm t) (qualExpr e)
> qualStmt (StmtDecl    ds) = StmtDecl `liftM` mapM qualDecl ds

> qualAlt :: Qual Alt
> qualAlt (Alt p t rhs) = liftM2 (Alt p) (qualTerm t) (qualRhs rhs)

> qualFieldExpr :: Qual (Field Expression)
> qualFieldExpr (Field p l e) = Field p l `liftM` qualExpr e

> qualOp :: Qual InfixOp
> qualOp (InfixOp     op) = InfixOp     `liftM` qualIdent op
> qualOp (InfixConstr op) = InfixConstr `liftM` qualIdent op

> qualIdent :: Qual QualIdent
> qualIdent x = do
>   m     <- R.asks moduleIdent
>   tyEnv <- R.asks valueEnv
>   return $ case isQualified x || isGlobal x of
>     False -> x
>     True  -> case qualLookupValue x tyEnv of
>       [y] -> origName y
>       _   -> case qualLookupValue qmx tyEnv of
>         [y] -> origName y
>         _   -> qmx
>       where qmx = qualQualify m x
>   where isGlobal = (== 0) . uniqueId . unqualify

> qualConstructor :: Qual QualIdent
> qualConstructor x = do
>   m     <- R.asks moduleIdent
>   tcEnv <- R.asks tyConsEnv
>   return $ case qualLookupTC x tcEnv of
>     [y] -> origName y
>     _   -> case qualLookupTC qmx tcEnv of
>       [y] -> origName y
>       _   -> qmx
>       where qmx = qualQualify m x

\end{verbatim}
