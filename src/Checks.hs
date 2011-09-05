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
-- In addition, nullary type constructors and type variables are dinstiguished
kindCheck :: CompilerEnv -> Module -> (CompilerEnv, Module)
kindCheck env (Module m es is ds)
  | null msgs = (env, Module m es is ds')
  | otherwise = errorMessages msgs
  where (ds', msgs) = KC.kindCheck (moduleIdent env) (tyConsEnv env) ds

-- |Apply the precendences of infix operators.
-- This function reanrranges the AST.
precCheck :: CompilerEnv -> Module -> (CompilerEnv, Module)
precCheck env (Module m es is ds)
  | null msgs = (env { opPrecEnv = pEnv' }, Module m es is ds')
  | otherwise = errorMessages msgs
  where (ds', pEnv', msgs) = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Apply the syntax check.
syntaxCheck :: Options -> CompilerEnv -> Module -> (CompilerEnv, Module)
syntaxCheck opts env (Module m es is ds)
  | null msgs = (env, Module m es is ds')
  | otherwise = errorMessages msgs
  where (ds', msgs) = SC.syntaxCheck opts (moduleIdent env) (aliasEnv env)
                   (arityEnv env) (valueEnv env) (tyConsEnv env) ds

-- |Apply the type check.
typeCheck :: CompilerEnv -> Module -> (CompilerEnv, Module)
typeCheck env mdl@(Module _ _ _ ds) = (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, mdl)
  where (tcEnv', tyEnv') = TC.typeCheck (moduleIdent env)
                              (tyConsEnv env) (valueEnv env) ds

-- TODO: Which kind of warnings?

-- |Check for warnings.
warnCheck :: CompilerEnv -> Module -> [Message]
warnCheck env (Module _ _ is ds)
  = WC.warnCheck (moduleIdent env) (valueEnv env) is ds
