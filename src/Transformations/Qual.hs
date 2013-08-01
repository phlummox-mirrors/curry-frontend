{- |
    Module      :  $Header$
    Description :  Proper Qualification
    Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2011 - 2012 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    After checking the module and before starting the translation into the
    intermediate language, the compiler properly qualifies all type
    constructors, data constructors and (global) functions
    occurring in a pattern or expression such that their module prefix
    matches the module of their definition.
    This is done also for functions and constructors declared
    in the current module.
    Only functions and variables declared in local declarations groups
    as well as function arguments remain unchanged.
-}

module Transformations.Qual (qual) where

import           Control.Monad             (liftM, liftM2, liftM3, liftM4, liftM5)
import qualified Control.Monad.Reader as R (Reader, asks, runReader)

import Curry.Base.Ident
import Curry.Syntax

import Base.TopEnv         (origName)

import Env.TypeConstructor (TCEnv   , qualLookupTC)
import Env.Value           (ValueEnv, qualLookupValue)

data QualEnv = QualEnv
  { moduleIdent :: ModuleIdent
  , tyConsEnv   :: TCEnv
  , valueEnv    :: ValueEnv
  }

type Qual a = a -> R.Reader QualEnv a

qual :: ModuleIdent -> TCEnv -> ValueEnv -> [Decl] -> [Decl]
qual m tcEnv tyEnv ds = R.runReader (mapM qDecl ds) (QualEnv m tcEnv tyEnv)

qDecl :: Qual Decl
qDecl i@(InfixDecl     _ _ _ _) = return i
qDecl (DataDecl      p n vs cs) = DataDecl p n vs `liftM` mapM qConstrDecl cs
qDecl (NewtypeDecl   p n vs nc) = NewtypeDecl p n vs `liftM` qNewConstrDecl nc
qDecl (TypeDecl      p n vs ty) = TypeDecl p n vs `liftM` qTypeExpr ty
qDecl (TypeSig    p b fs cx ty) = TypeSig p b fs cx `liftM` qTypeExpr ty
qDecl (FunctionDecl p cty id0 f eqs) = FunctionDecl p cty id0 f `liftM` mapM qEquation eqs
qDecl (ForeignDecl  p c x n ty) = ForeignDecl p c x n `liftM` qTypeExpr ty
qDecl e@(ExternalDecl      _ _) = return e
qDecl (PatternDecl p cty id0 t rhs)
  = liftM2 (PatternDecl p cty id0) (qPattern t) (qRhs rhs)
qDecl vs@(FreeDecl   _ _) = return vs
qDecl (ClassDecl p scon cls ty decls) 
  = liftM4 (ClassDecl p) (qSContext scon) (return cls) (return ty) 
           (mapM qDecl decls)
qDecl (InstanceDecl p scon cls ty ids decls) 
  = liftM5 (InstanceDecl p) (qSContext scon) (qIdent cls) (qTConstr ty) 
           (return ids) (mapM qDecl decls) 

qConstrDecl :: Qual ConstrDecl
qConstrDecl (ConstrDecl     p vs n tys)
  = ConstrDecl p vs n `liftM` mapM qTypeExpr tys
qConstrDecl (ConOpDecl p vs ty1 op ty2)
  = liftM2 (flip (ConOpDecl p vs) op) (qTypeExpr ty1) (qTypeExpr ty2)

qNewConstrDecl :: Qual NewConstrDecl
qNewConstrDecl (NewConstrDecl p vs n ty)
  = NewConstrDecl p vs n `liftM` qTypeExpr ty

qTypeExpr :: Qual TypeExpr
qTypeExpr (ConstructorType c tys)
  = liftM2 ConstructorType (qConstr c) (mapM qTypeExpr tys)
qTypeExpr (SpecialConstructorType (QualTC c) tys)
  = liftM2 SpecialConstructorType (QualTC `liftM` qConstr c) (mapM qTypeExpr tys)
qTypeExpr (SpecialConstructorType c tys)
  = liftM (SpecialConstructorType c) (mapM qTypeExpr tys) 
qTypeExpr v@(VariableType      _) = return v
qTypeExpr (TupleType         tys) = TupleType `liftM` mapM qTypeExpr tys
qTypeExpr (ListType           ty) = ListType `liftM` qTypeExpr ty
qTypeExpr (ArrowType     ty1 ty2)
  = liftM2 ArrowType (qTypeExpr ty1) (qTypeExpr ty2)
qTypeExpr (RecordType     fs rty)
  = liftM2 RecordType (mapM qFieldType fs) (qRecordType rty)
  where
  qFieldType (ls, ty)  = (\ ty' -> (ls, ty')) `liftM` qTypeExpr ty
  qRecordType Nothing  = return Nothing
  qRecordType (Just v) = Just `liftM` qTypeExpr v

qEquation :: Qual Equation
qEquation (Equation p lhs rhs) = liftM2 (Equation p) (qLhs lhs) (qRhs rhs)

qLhs :: Qual Lhs
qLhs (FunLhs    f ts) = FunLhs f `liftM` mapM qPattern ts
qLhs (OpLhs t1 op t2) = liftM2 (flip OpLhs op) (qPattern t1) (qPattern t2)
qLhs (ApLhs   lhs ts) = liftM2 ApLhs (qLhs lhs) (mapM qPattern ts)

qPattern :: Qual Pattern
qPattern l@(LiteralPattern        _) = return l
qPattern n@(NegativePattern     _ _) = return n
qPattern v@(VariablePattern       _) = return v
qPattern (ConstructorPattern   c ts)
  = liftM2 ConstructorPattern (qIdent c) (mapM qPattern ts)
qPattern (InfixPattern     t1 op t2)
  = liftM3 InfixPattern (qPattern t1) (qIdent op) (qPattern t2)
qPattern (ParenPattern            t) = ParenPattern `liftM` qPattern t
qPattern (TuplePattern         p ts) = TuplePattern p `liftM` mapM qPattern ts
qPattern (ListPattern          p ts) = ListPattern  p `liftM` mapM qPattern ts
qPattern (AsPattern             v t) = AsPattern    v `liftM` qPattern t
qPattern (LazyPattern           p t) = LazyPattern  p `liftM` qPattern t
qPattern (FunctionPattern      f ts)
  = liftM2 FunctionPattern (qIdent f) (mapM qPattern ts)
qPattern (InfixFuncPattern t1 op t2)
  = liftM3 InfixFuncPattern (qPattern t1) (qIdent op) (qPattern t2)
qPattern (RecordPattern       fs rt)
  = liftM2 RecordPattern (mapM qFieldPattern fs) (qRecordTerm rt)
  where qRecordTerm Nothing  = return Nothing
        qRecordTerm (Just v) = Just `liftM` qPattern v

qFieldPattern :: Qual (Field Pattern)
qFieldPattern (Field p l t) = Field p l `liftM` qPattern t

qRhs :: Qual Rhs
qRhs (SimpleRhs p e ds) = liftM2 (SimpleRhs p) (qExpr e) (mapM qDecl ds)
qRhs (GuardedRhs es ds)
  = liftM2 GuardedRhs (mapM qCondExpr es) (mapM qDecl ds)

qCondExpr :: Qual CondExpr
qCondExpr (CondExpr p g e) = liftM2 (CondExpr p) (qExpr g) (qExpr e)

qExpr :: Qual Expression
qExpr l@(Literal             _) = return l
qExpr (Variable          cty v) = Variable cty `liftM` qIdent v
qExpr (Constructor           c) = Constructor `liftM` qIdent c
qExpr (Paren                 e) = Paren `liftM` qExpr e
qExpr (Typed       cty e cx ty) = liftM3 (Typed cty) (qExpr e) (return cx) (qTypeExpr ty)
qExpr (Tuple              p es) = Tuple p `liftM` mapM qExpr es
qExpr (List               p es) = List p `liftM` mapM qExpr es
qExpr (ListCompr        p e qs) = liftM2 (ListCompr p) (qExpr e)
                                                       (mapM qStmt qs)
qExpr (EnumFrom              e) = EnumFrom `liftM` qExpr e
qExpr (EnumFromThen      e1 e2) = liftM2 EnumFromThen   (qExpr e1) (qExpr e2)
qExpr (EnumFromTo        e1 e2) = liftM2 EnumFromTo     (qExpr e1) (qExpr e2)
qExpr (EnumFromThenTo e1 e2 e3) = liftM3 EnumFromThenTo (qExpr e1) (qExpr e2)
                                                        (qExpr e3)
qExpr (UnaryMinus         op e) = UnaryMinus op `liftM` qExpr e
qExpr (Apply             e1 e2) = liftM2 Apply (qExpr e1) (qExpr e2)
qExpr (InfixApply     e1 op e2) = liftM3 InfixApply (qExpr e1) (qInfixOp op)
                                                               (qExpr e2)
qExpr (LeftSection        e op) = liftM2 LeftSection  (qExpr e) (qInfixOp op)
qExpr (RightSection       op e) = liftM2 RightSection (qInfixOp op) (qExpr e)
qExpr (Lambda           r ts e) = liftM2 (Lambda r) (mapM qPattern ts)
                                                    (qExpr e)
qExpr (Let                ds e) = liftM2 Let (mapM qDecl ds) (qExpr e)
qExpr (Do                sts e) = liftM2 Do (mapM qStmt sts) (qExpr e)
qExpr (IfThenElse   r e1 e2 e3) = liftM3 (IfThenElse r) (qExpr e1)
                                         (qExpr e2) (qExpr e3)
qExpr (Case          r ct e as) = liftM2 (Case r ct) (qExpr e) (mapM qAlt as)
qExpr (RecordConstr         fs) = RecordConstr `liftM` mapM qFieldExpr fs
qExpr (RecordSelection     e l) = flip RecordSelection l `liftM` qExpr e
qExpr (RecordUpdate       fs e) = liftM2 RecordUpdate (mapM qFieldExpr fs)
                                                      (qExpr e)

qStmt :: Qual Statement
qStmt (StmtExpr p   e) = StmtExpr p `liftM` qExpr e
qStmt (StmtBind p t e) = liftM2 (StmtBind p) (qPattern t) (qExpr e)
qStmt (StmtDecl    ds) = StmtDecl `liftM` mapM qDecl ds

qAlt :: Qual Alt
qAlt (Alt p t rhs) = liftM2 (Alt p) (qPattern t) (qRhs rhs)

qFieldExpr :: Qual (Field Expression)
qFieldExpr (Field p l e) = Field p l `liftM` qExpr e

qInfixOp :: Qual InfixOp
qInfixOp (InfixOp cty op) = InfixOp cty `liftM` qIdent op
qInfixOp (InfixConstr op) = InfixConstr `liftM` qIdent op

qIdent :: Qual QualIdent
qIdent x = do
  m     <- R.asks moduleIdent
  tyEnv <- R.asks valueEnv
  return $ case isQualified x || hasGlobalScope (unqualify x) of
    False -> x
    True  -> case qualLookupValue x tyEnv of
      [y] -> origName y
      _   -> case qualLookupValue qmx tyEnv of
        [y] -> origName y
        _   -> qmx
      where qmx = qualQualify m x

qConstr :: Qual QualIdent
qConstr x = do
  m     <- R.asks moduleIdent
  tcEnv <- R.asks tyConsEnv
  return $ case qualLookupTC x tcEnv of
    [y] -> origName y
    _   -> case qualLookupTC qmx tcEnv of
      [y] -> origName y
      _   -> qmx
      where qmx = qualQualify m x

      
qSContext :: Qual SContext
qSContext (SContext cs) = do
  list <- mapM (\(qid, id0) -> do qid' <- qIdent qid; return (qid', id0)) cs 
  return $ SContext list 
  
qTConstr :: Qual TypeConstructor
qTConstr (QualTC qid) = do
  qid' <- qIdent qid 
  return $ QualTC qid'
qTConstr con = return con

