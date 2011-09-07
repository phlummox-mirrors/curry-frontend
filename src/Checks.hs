{- |
    Module      :  $Header$
    Description :  Different checks on a Curry module
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different checks to be performed on a Curry
    module during compilation, e.g. type checking.
-}
module Checks where

import Curry.Syntax (Module (..))

import Base.Messages

import qualified Checks.KindCheck   as KC (kindCheck)
import qualified Checks.PrecCheck   as PC (precCheck)
import qualified Checks.SyntaxCheck as SC (syntaxCheck)
import qualified Checks.TypeCheck   as TC (typeCheck)
import qualified Checks.WarnCheck   as WC (warnCheck)

import CompilerEnv
import CompilerOpts

data CheckStatus a
  = CheckFailed [Message]
  | CheckSuccess a

instance Monad CheckStatus where
  return  = CheckSuccess
  m >>= f = case m of
    CheckFailed  errs -> CheckFailed  errs
    CheckSuccess    a -> f a

-- TODO: More documentation

-- |Check the kinds of type definitions and signatures.
-- In addition, nullary type constructors and type variables are
-- disambiguated in the declarations; the environment remains unchanged.
kindCheck :: CompilerEnv -> Module -> (CompilerEnv, Module)
kindCheck env (Module m es is ds)
  | null msgs = (env, Module m es is ds')
  | otherwise = errorMessages msgs
  where (ds', msgs) = KC.kindCheck (moduleIdent env) (tyConsEnv env) ds

-- |Check for a correct syntax.
-- In addition, nullary data constructors and variables are
-- disambiguated in the declarations; the environment remains unchanged.
syntaxCheck :: Options -> CompilerEnv -> Module -> (CompilerEnv, Module)
syntaxCheck opts env (Module m es is ds)
  | null msgs = (env, Module m es is ds')
  | otherwise = errorMessages msgs
  where (ds', msgs) = SC.syntaxCheck opts (moduleIdent env)
                      (valueEnv env) (tyConsEnv env) ds

-- |Check the precedences of infix operators.
-- In addition, the abstract syntax tree is rearranged to reflect the
-- relative precedences; the operator precedence environment is updated.
precCheck :: CompilerEnv -> Module -> (CompilerEnv, Module)
precCheck env (Module m es is ds)
  | null msgs = (env { opPrecEnv = pEnv' }, Module m es is ds')
  | otherwise = errorMessages msgs
  where (ds', pEnv', msgs) = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Apply the correct typing of the module.
-- The declarations remain unchanged; the type constructor and value
-- environments are updated.
typeCheck :: CompilerEnv -> Module -> (CompilerEnv, Module)
typeCheck env mdl@(Module _ _ _ ds) =
  (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, mdl)
  where (tcEnv', tyEnv') = TC.typeCheck (moduleIdent env)
                              (tyConsEnv env) (valueEnv env) ds

-- TODO: Which kind of warnings?

-- |Check for warnings.
warnCheck :: CompilerEnv -> Module -> [Message]
warnCheck env mdl = WC.warnCheck (valueEnv env) mdl
