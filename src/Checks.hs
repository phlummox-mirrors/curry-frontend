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

import Curry.Base.MessageMonad (Message)
import Curry.Syntax

import qualified Checks.KindCheck   as KC (kindCheck)
import qualified Checks.PrecCheck   as PC (precCheck)
import qualified Checks.SyntaxCheck as SC (syntaxCheck)
import qualified Checks.TypeCheck   as TC (typeCheck)
import qualified Checks.WarnCheck   as WC (warnCheck)

import CompilerEnv
import CompilerOpts

-- TODO: More documentation

-- |Check the kinds of type definitions and signatures.
-- In addition, nullary type constructors and type variables are dinstiguished
kindCheck :: Module -> CompilerEnv -> (Module, CompilerEnv)
kindCheck (Module m es is ds) env = (Module m es is ds', env)
  where ds' = KC.kindCheck (moduleIdent env) (tyConsEnv env) ds

-- |Apply the precendences of infix operators.
-- This function reanrranges the AST.
precCheck :: Module -> CompilerEnv -> (Module, CompilerEnv)
precCheck (Module m es is ds) env = (Module m es is ds', env { opPrecEnv = pEnv' })
  where (pEnv', ds') = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Apply the syntax check.
syntaxCheck :: Options -> Module -> CompilerEnv -> (Module, CompilerEnv)
syntaxCheck opts (Module m es is ds) env = (Module m es is ds', env)
  where ds'     = SC.syntaxCheck withExt (moduleIdent env) (aliasEnv env)
                   (arityEnv env) (valueEnv env) (tyConsEnv env) ds
        withExt = BerndExtension `elem` optExtensions opts

-- |Apply the type check.
typeCheck :: Module -> CompilerEnv -> (Module, CompilerEnv)
typeCheck mdl@(Module _ _ _ ds) env = (mdl, env { tyConsEnv = tcEnv', valueEnv = tyEnv' })
  where (tcEnv', tyEnv') = TC.typeCheck (moduleIdent env)
                              (tyConsEnv env) (valueEnv env) ds

-- TODO: Which kind of warnings?

-- |Check for warnings.
warnCheck :: Module -> CompilerEnv -> [Message]
warnCheck (Module _ _ is ds) env
  = WC.warnCheck (moduleIdent env) (valueEnv env) is ds
