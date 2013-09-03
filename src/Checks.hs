{- |
    Module      :  $Header$
    Description :  Different checks on a Curry module
    Copyright   :  (c) 2011 - 2013, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different checks to be performed on a Curry
    module during compilation, e.g. type checking.
-}
module Checks where

import qualified Checks.InterfaceCheck as IC (interfaceCheck)
import qualified Checks.ExportCheck    as EC (exportCheck)
import qualified Checks.KindCheck      as KC (kindCheck)
import qualified Checks.PrecCheck      as PC (precCheck)
import qualified Checks.SyntaxCheck    as SC (syntaxCheck)
import qualified Checks.TypeCheck      as TC (typeCheck)
import qualified Checks.WarnCheck      as WC (warnCheck)

import Curry.Syntax (Module (..), Interface (..))

import Base.Messages
import CompilerEnv
import CompilerOpts

type Check m a = Options -> CompilerEnv -> a -> CYT m (CompilerEnv, a)

interfaceCheck :: Monad m => Check m Interface
interfaceCheck _ env intf
  | null msgs = right (env, intf)
  | otherwise = left msgs
  where msgs = IC.interfaceCheck (opPrecEnv env) (tyConsEnv env)
                                 (valueEnv env) intf

-- |Check the kinds of type definitions and signatures.
--
-- * Declarations: Nullary type constructors and type variables are
--                 disambiguated
-- * Environment:  remains unchanged
kindCheck :: Monad m => Check m Module
kindCheck _ env (Module m es is ds)
  | null msgs = right (env, Module m es is ds')
  | otherwise = left msgs
  where (ds', msgs) = KC.kindCheck (moduleIdent env) (tyConsEnv env) ds

-- |Check for a correct syntax.
--
-- * Declarations: Nullary data constructors and variables are
--                 disambiguated, variables are renamed
-- * Environment:  remains unchanged
syntaxCheck :: Monad m => Check m Module
syntaxCheck opts env (Module m es is ds)
  | null msgs = right (env, Module m es is ds')
  | otherwise = left msgs
  where (ds', msgs) = SC.syntaxCheck opts (moduleIdent env)
                      (valueEnv env) (tyConsEnv env) ds

-- |Check the precedences of infix operators.
--
-- * Declarations: Expressions are reordered according to the specified
--                 precedences
-- * Environment:  The operator precedence environment is updated
precCheck :: Monad m => Check m Module
precCheck _ env (Module m es is ds)
  | null msgs = right (env { opPrecEnv = pEnv' }, Module m es is ds')
  | otherwise = left msgs
  where (ds', pEnv', msgs) = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Apply the correct typing of the module.
-- The declarations remain unchanged; the type constructor and value
-- environments are updated.
typeCheck :: Monad m => Check m Module
typeCheck _ env mdl@(Module _ _ _ ds)
  | null msgs = right (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, mdl)
  | otherwise = left msgs
  where (tcEnv', tyEnv', msgs) = TC.typeCheck (moduleIdent env)
                                 (tyConsEnv env) (valueEnv env) ds

-- |Check the export specification
exportCheck :: Monad m => Check m Module
exportCheck _ env (Module m es is ds)
  | null msgs = right (env, Module m es' is ds)
  | otherwise = left msgs
  where (es', msgs) = EC.exportCheck (moduleIdent env) (aliasEnv env)
                                     (tyConsEnv env) (valueEnv env) es

-- TODO: Which kind of warnings?

-- |Check for warnings.
warnCheck :: Options -> CompilerEnv -> Module -> [Message]
warnCheck opts env mdl = WC.warnCheck opts (valueEnv env) (tyConsEnv env) mdl
