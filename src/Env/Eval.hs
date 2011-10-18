{- |
    Module      :  $Header$
    Description :  Environment of Evaluation Annotations
    Copyright   :  (c) 2001-2004, Wolfgang Lux
                       2011, Björn Peemöller   (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module computes the evaluation annotation environment. There is no
    need to check the annotations because this happens already while checking
    the definitions of the module.
-}

module Env.Eval (EvalEnv, initEEnv, evalEnv) where

import qualified Data.Map as Map (Map, empty, insert)

import Curry.Base.Ident (Ident)
import Curry.Syntax

type EvalEnv = Map.Map Ident EvalAnnotation

initEEnv :: EvalEnv
initEEnv = Map.empty

-- |The function 'evalEnv' collects all evaluation annotations of
-- the module by traversing the syntax tree.
evalEnv :: Module -> EvalEnv
evalEnv (Module _ _ _ ds) = foldr annDecl initEEnv ds

annDecl :: Decl -> EvalEnv -> EvalEnv
annDecl (EvalAnnot    _ fs ev) env = foldr (`Map.insert` ev) env fs
annDecl (FunctionDecl _ _ eqs) env = foldr annEquation env eqs
annDecl (PatternDecl  _ _ rhs) env = annRhs rhs env
annDecl _                      env = env

annEquation :: Equation -> EvalEnv -> EvalEnv
annEquation (Equation _ _ rhs) = annRhs rhs

annRhs :: Rhs -> EvalEnv -> EvalEnv
annRhs (SimpleRhs _ e ds) env = annExpr e (foldr annDecl env ds)
annRhs (GuardedRhs es ds) env = foldr annCondExpr (foldr annDecl env ds) es

annCondExpr :: CondExpr -> EvalEnv -> EvalEnv
annCondExpr (CondExpr _ g e) env = annExpr g (annExpr e env)

annExpr :: Expression -> EvalEnv -> EvalEnv
annExpr (Literal               _) env = env
annExpr (Variable              _) env = env
annExpr (Constructor           _) env = env
annExpr (Paren                 e) env = annExpr e env
annExpr (Typed               e _) env = annExpr e env
annExpr (Tuple              _ es) env = foldr annExpr env es
annExpr (List               _ es) env = foldr annExpr env es
annExpr (ListCompr        _ e qs) env = annExpr e (foldr annStatement env qs)
annExpr (EnumFrom              e) env = annExpr e env
annExpr (EnumFromThen      e1 e2) env = annExpr e1 (annExpr e2 env)
annExpr (EnumFromTo        e1 e2) env = annExpr e1 (annExpr e2 env)
annExpr (EnumFromThenTo e1 e2 e3) env = annExpr e1 (annExpr e2 (annExpr e3 env))
annExpr (UnaryMinus          _ e) env = annExpr e env
annExpr (Apply             e1 e2) env = annExpr e1 (annExpr e2 env)
annExpr (InfixApply      e1 _ e2) env = annExpr e1 (annExpr e2 env)
annExpr (LeftSection         e _) env = annExpr e env
annExpr (RightSection        _ e) env = annExpr e env
annExpr (Lambda            _ _ e) env = annExpr e env
annExpr (Let                ds e) env = foldr annDecl (annExpr e env) ds
annExpr (Do                sts e) env = foldr annStatement (annExpr e env) sts
annExpr (IfThenElse   _ e1 e2 e3) env = annExpr e1 (annExpr e2 (annExpr e3 env))
annExpr (Case           _ e alts) env = annExpr e (foldr annAlt env alts)
annExpr (RecordConstr         fs) env = foldr (annExpr . fieldTerm) env fs
annExpr (RecordSelection     e _) env = annExpr e env
annExpr (RecordUpdate       fs e) env = foldr (annExpr . fieldTerm) (annExpr e env) fs

annStatement :: Statement -> EvalEnv -> EvalEnv
annStatement (StmtExpr   _ e) env = annExpr e env
annStatement (StmtDecl    ds) env = foldr annDecl env ds
annStatement (StmtBind _ _ e) env = annExpr e env

annAlt :: Alt -> EvalEnv -> EvalEnv
annAlt (Alt _ _ rhs) = annRhs rhs
