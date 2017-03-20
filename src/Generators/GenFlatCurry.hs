{- |
    Module      :  $Header$
    Description :  Generation of FlatCurry program and interface terms
    Copyright   :  (c) 2017        Finn Teegen
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of a 'FlatCurry' program term or
    a 'FlatCurry' interface out of an 'Annotated FlatCurry' module.
-}
module Generators.GenFlatCurry (genFlatCurry, genFlatInterface) where

import Curry.FlatCurry.Goodies
import Curry.FlatCurry.Type
import Curry.FlatCurry.Annotated.Goodies
import Curry.FlatCurry.Annotated.Type

-- transforms annotated FlatCurry code to FlatCurry code
genFlatCurry :: AProg a -> Prog
genFlatCurry = trAProg
  (\name imps types funcs ops ->
    Prog name imps types (map genFlatFuncDecl funcs) ops)

genFlatFuncDecl :: AFuncDecl a -> FuncDecl
genFlatFuncDecl = trAFunc
  (\name arity vis t rule -> Func name arity vis t $ genFlatRule rule)

genFlatRule :: ARule a -> Rule
genFlatRule = trARule
  (\_ args e -> Rule (map fst args) $ genFlatExpr e)
  (const External)

genFlatExpr :: AExpr a -> Expr
genFlatExpr = trAExpr
  (const Var)
  (const Lit)
  (\_ ct name args -> Comb ct (fst name) args)
  (\_ bs e -> Let (map (\(v, e') -> (fst v, e')) bs) e)
  (\_ vs e -> Free (map fst vs) e)
  (\_ e1 e2 -> Or e1 e2)
  (\_ ct e bs -> Case ct e bs)
  (\pat e -> Branch (genFlatPattern pat) e)
  (\_ e ty -> Typed e ty)

genFlatPattern :: APattern a -> Pattern
genFlatPattern = trAPattern
  (\_ name args -> Pattern (fst name) $ map fst args)
  (const LPattern)

-- transforms a FlatCurry module to a FlatCurry interface
genFlatInterface :: Prog -> Prog
genFlatInterface =
  updProgFuncs $ map $ updFuncRule $ const $ Rule [] $ Var 0
