{- |
    Module      :  $Header$
    Description :  Extraction of free and bound variables
    Copyright   :  (c)             Wolfgang Lux
                       2011 - 2012 Björn Peemöller
                       2015        Jan Tikovsky
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler needs to compute the lists of free and bound variables for
    various different entities. We will devote three type classes to that
    purpose. The 'QualExpr' class is expected to take into account
    that it is possible to use a qualified name to refer to a function
    defined in the current module and therefore @M.x@ and @x@, where
    @M@ is the current module name, should be considered the same name.
    However, note that this is correct only after renaming all local
    definitions as @M.x@ always denotes an entity defined at the
    top-level.
-}
module Base.Expr (Expr (..), QualExpr (..), QuantExpr (..)) where

import           Data.List        (nub)
import qualified Data.Set  as Set (fromList, notMember)

import Curry.Base.Ident
import Curry.Syntax

class Expr e where
  -- |Free variables in an 'Expr'
  fv :: e -> [Ident]

class QualExpr e where
  -- |Free qualified variables in an 'Expr'
  qfv :: ModuleIdent -> e -> [Ident]

class QuantExpr e where
  -- |Bounded variables in an 'Expr'
  bv :: e -> [Ident]

instance Expr e => Expr [e] where
  fv = concatMap fv

instance QualExpr e => QualExpr [e] where
  qfv m = concatMap (qfv m)

instance QuantExpr e => QuantExpr [e] where
  bv = concatMap bv

-- The 'Decl' instance of 'QualExpr' returns all free
-- variables on the right hand side, regardless of whether they are bound
-- on the left hand side. This is more convenient as declarations are
-- usually processed in a declaration group where the set of free
-- variables cannot be computed independently for each declaration. Also
-- note that the operator in a unary minus expression is not a free
-- variable. This operator always refers to a global function from the
-- prelude.

instance QualExpr Decl where
  qfv m (FunctionDecl _ _ eqs) = qfv m eqs
  qfv m (PatternDecl  _ _ rhs) = qfv m rhs
  qfv _ _                      = []

instance QuantExpr Decl where
  bv (TypeSig        _ vs _) = vs
  bv (FunctionDecl    _ f _) = [f]
  bv (ForeignDecl _ _ _ f _) = [f]
  bv (ExternalDecl     _ fs) = fs
  bv (PatternDecl     _ t _) = bv t
  bv (FreeDecl         _ vs) = vs
  bv _                       = []

instance QualExpr Equation where
  qfv m (Equation _ lhs rhs) = filterBv lhs $ qfv m lhs ++ qfv m rhs

instance QuantExpr Lhs where
  bv = bv . snd . flatLhs

instance QualExpr Lhs where
  qfv m lhs = qfv m $ snd $ flatLhs lhs

instance QualExpr Rhs where
  qfv m (SimpleRhs _ e ds) = filterBv ds $ qfv m e  ++ qfv m ds
  qfv m (GuardedRhs es ds) = filterBv ds $ qfv m es ++ qfv m ds

instance QualExpr CondExpr where
  qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

instance QualExpr Expression where
  qfv _ (Literal               _) = []
  qfv m (Variable              v) = maybe [] return $ localIdent m v
  qfv _ (Constructor           _) = []
  qfv m (Paren                 e) = qfv m e
  qfv m (Typed               e _) = qfv m e
  qfv m (Tuple              _ es) = qfv m es
  qfv m (List               _ es) = qfv m es
  qfv m (ListCompr        _ e qs) = foldr (qfvStmt m) (qfv m e) qs
  qfv m (EnumFrom              e) = qfv m e
  qfv m (EnumFromThen      e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (EnumFromTo        e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
  qfv m (UnaryMinus          _ e) = qfv m e
  qfv m (Apply             e1 e2) = qfv m e1 ++ qfv m e2
  qfv m (InfixApply     e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
  qfv m (LeftSection        e op) = qfv m op ++ qfv m e
  qfv m (RightSection       op e) = qfv m op ++ qfv m e
  qfv m (Lambda           _ ts e) = filterBv ts $ qfv m e
  qfv m (Let                ds e) = filterBv ds $ qfv m ds ++ qfv m e
  qfv m (Do                sts e) = foldr (qfvStmt m) (qfv m e) sts
  qfv m (IfThenElse   _ e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
  qfv m (Case         _ _ e alts) = qfv m e ++ qfv m alts
  qfv m (RecordConstr       _ fs) = qfv m fs
  qfv m (RecordUpdate       e fs) = qfv m e ++ qfv m fs

qfvStmt :: ModuleIdent -> Statement -> [Ident] -> [Ident]
qfvStmt m st fvs = qfv m st ++ filterBv st fvs

instance QualExpr Statement where
  qfv m (StmtExpr   _ e) = qfv m e
  qfv m (StmtDecl    ds) = filterBv ds $ qfv m ds
  qfv m (StmtBind _ _ e) = qfv m e

instance QualExpr Alt where
  qfv m (Alt _ t rhs) = filterBv t $ qfv m rhs

instance QuantExpr a => QuantExpr (Field a) where
  bv (Field _ _ t) = bv t

instance QualExpr a => QualExpr (Field a) where
  qfv m (Field _ _ t) = qfv m t

instance QuantExpr Statement where
  bv (StmtExpr   _ _) = []
  bv (StmtBind _ t _) = bv t
  bv (StmtDecl    ds) = bv ds

instance QualExpr InfixOp where
  qfv m (InfixOp    op) = qfv m $ Variable op
  qfv _ (InfixConstr _) = []

instance QuantExpr Pattern where
  bv (LiteralPattern         _) = []
  bv (NegativePattern      _ _) = []
  bv (VariablePattern        v) = [v]
  bv (ConstructorPattern  _ ts) = bv ts
  bv (InfixPattern     t1 _ t2) = bv t1 ++ bv t2
  bv (ParenPattern           t) = bv t
  bv (TuplePattern        _ ts) = bv ts
  bv (ListPattern         _ ts) = bv ts
  bv (AsPattern            v t) = v : bv t
  bv (LazyPattern          _ t) = bv t
  bv (FunctionPattern     _ ts) = nub $ bv ts
  bv (InfixFuncPattern t1 _ t2) = nub $ bv t1 ++ bv t2
  bv (RecordPattern       _ fs) = bv fs

instance QualExpr Pattern where
  qfv _ (LiteralPattern          _) = []
  qfv _ (NegativePattern       _ _) = []
  qfv _ (VariablePattern         _) = []
  qfv m (ConstructorPattern   _ ts) = qfv m ts
  qfv m (InfixPattern      t1 _ t2) = qfv m [t1, t2]
  qfv m (ParenPattern            t) = qfv m t
  qfv m (TuplePattern         _ ts) = qfv m ts
  qfv m (ListPattern          _ ts) = qfv m ts
  qfv m (AsPattern            _ ts) = qfv m ts
  qfv m (LazyPattern           _ t) = qfv m t
  qfv m (FunctionPattern      f ts)
    = maybe [] return (localIdent m f) ++ qfv m ts
  qfv m (InfixFuncPattern t1 op t2)
    = maybe [] return (localIdent m op) ++ qfv m [t1, t2]
  qfv m (RecordPattern        _ fs) = qfv m fs

instance Expr TypeExpr where
  fv (ConstructorType _ tys) = fv tys
  fv (VariableType       tv)
    | isAnonId tv            = []
    | otherwise              = [tv]
  fv (TupleType         tys) = fv tys
  fv (ListType           ty) = fv ty
  fv (ArrowType     ty1 ty2) = fv ty1 ++ fv ty2

filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
filterBv e = filter (`Set.notMember` Set.fromList (bv e))

-- Since multiple variable occurrences are allowed in function patterns,
-- it is necessary to compute the list of bound variables in a different way:
-- Each variable occuring in the function pattern will be unique in the result
-- list.

--  bv (FunctionPattern      f ts) = bvFuncPatt $ FunctionPattern f ts
--  bv (InfixFuncPattern t1 op t2) = bvFuncPatt $ InfixFuncPattern t1 op t2

-- bvFuncPatt :: Pattern -> [Ident]
-- bvFuncPatt = bvfp []
--  where
--  bvfp bvs (LiteralPattern         _) = bvs
--  bvfp bvs (NegativePattern      _ _) = bvs
--  bvfp bvs (VariablePattern        v)
--     | v `elem` bvs                   = bvs
--     | otherwise                      = v : bvs
--  bvfp bvs (ConstructorPattern  _ ts) = foldl bvfp bvs ts
--  bvfp bvs (InfixPattern     t1 _ t2) = foldl bvfp bvs [t1, t2]
--  bvfp bvs (ParenPattern           t) = bvfp bvs t
--  bvfp bvs (TuplePattern        _ ts) = foldl bvfp bvs ts
--  bvfp bvs (ListPattern         _ ts) = foldl bvfp bvs ts
--  bvfp bvs (AsPattern            v t)
--     | v `elem` bvs                   = bvfp bvs t
--     | otherwise                      = bvfp (v : bvs) t
--  bvfp bvs (LazyPattern          _ t) = bvfp bvs t
--  bvfp bvs (FunctionPattern     _ ts) = foldl bvfp bvs ts
--  bvfp bvs (InfixFuncPattern t1 _ t2) = foldl bvfp bvs [t1, t2]
--  bvfp bvs (RecordPattern       fs r)
--     = foldl bvfp (maybe bvs (bvfp bvs) r) (map fieldTerm fs)
