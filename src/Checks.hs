{- |
    Module      :  $Header$
    Description :  Different checks on a Curry module
    Copyright   :  (c) 2011 - 2013 Björn Peemöller
                       2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different checks to be performed on a Curry
    module during compilation, e.g. type checking.
-}
module Checks where

import qualified Checks.InterfaceCheck    as IC  (interfaceCheck)
import qualified Checks.ImportSyntaxCheck as ISC (importCheck)
import qualified Checks.ExportCheck       as EC  (exportCheck, expandExports)
import qualified Checks.ExtensionCheck    as EXC (extensionCheck)
import qualified Checks.KindCheck         as KC  (kindCheck)
import qualified Checks.PrecCheck         as PC  (precCheck)
import qualified Checks.SyntaxCheck       as SC  (syntaxCheck)
import qualified Checks.TypeCheck         as TC  (typeCheck)
import qualified Checks.TypeSyntaxCheck   as TSC (typeSyntaxCheck)
import qualified Checks.WarnCheck         as WC  (warnCheck)

import Curry.Base.Monad
import Curry.Syntax (Module (..), Interface (..), ImportSpec)

import Base.Messages
import CompilerEnv
import CompilerOpts

type Check m a = Options -> CompEnv a -> CYT m (CompEnv a)

interfaceCheck :: Monad m => Check m Interface
interfaceCheck _ (env, intf)
  | null msgs = ok (env, intf)
  | otherwise = failMessages msgs
  where msgs = IC.interfaceCheck (opPrecEnv env) (tyConsEnv env)
                                 (valueEnv env) intf

importCheck :: Monad m => Interface -> Maybe ImportSpec -> CYT m (Maybe ImportSpec)
importCheck intf is
  | null msgs = ok is'
  | otherwise = failMessages msgs
  where (is', msgs) = ISC.importCheck intf is

-- |Check for enabled language extensions.
--
-- * Declarations: remain unchanged
-- * Environment:  The enabled language extensions are updated
extensionCheck :: Monad m => Check m Module
extensionCheck opts (env, mdl)
  | null msgs = ok (env { extensions = exts }, mdl)
  | otherwise = failMessages msgs
  where (exts, msgs) = EXC.extensionCheck opts mdl

-- |Check the type syntax of type definitions and signatures.
--
-- * Declarations: Nullary type constructors and type variables are
--                 disambiguated
-- * Environment:  remains unchanged
typeSyntaxCheck :: Monad m => Check m Module
typeSyntaxCheck _ (env, mdl)
  | null msgs = ok (env, mdl')
  | otherwise = failMessages msgs
  where (mdl', msgs) = TSC.typeSyntaxCheck (tyConsEnv env) mdl

-- |Check the kinds of type definitions and signatures.
--
-- * Declarations: remains unchanged
-- * Environment:  The type constructor environment is updated
kindCheck :: Monad m => Check m Module
kindCheck _ (env, mdl)
  | null msgs = ok (env { tyConsEnv = tcEnv }, mdl)
  | otherwise = failMessages msgs
  where (tcEnv, msgs) = KC.kindCheck (tyConsEnv env) mdl

-- |Check for a correct syntax.
--
-- * Declarations: Nullary data constructors and variables are
--                 disambiguated, variables are renamed
-- * Environment:  remains unchanged
syntaxCheck :: Monad m => Check m Module
syntaxCheck opts (env, mdl)
  | null msgs = ok (env { extensions = exts }, mdl')
  | otherwise = failMessages msgs
  where ((mdl', exts), msgs) = SC.syntaxCheck opts (valueEnv env) mdl

-- |Check the precedences of infix operators.
--
-- * Declarations: Expressions are reordered according to the specified
--                 precedences
-- * Environment:  The operator precedence environment is updated
precCheck :: Monad m => Check m Module
precCheck _ (env, Module ps m es is ds)
  | null msgs = ok (env { opPrecEnv = pEnv' }, Module ps m es is ds')
  | otherwise = failMessages msgs
  where (ds', pEnv', msgs) = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Apply the correct typing of the module.
-- The declarations remain unchanged; the type constructor and value
-- environments are updated.
typeCheck :: Monad m => Check m Module
typeCheck _ (env, mdl@(Module _ _ _ _ ds))
  | null msgs = ok (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, mdl)
  | otherwise = failMessages msgs
  where (tcEnv', tyEnv', msgs) = TC.typeCheck (moduleIdent env)
                                 (tyConsEnv env) (valueEnv env) ds

-- |Check the export specification
exportCheck :: Monad m => Check m Module
exportCheck _ (env, mdl@(Module _ _ es _ _))
  | null msgs = ok (env, mdl)
  | otherwise = failMessages msgs
  where msgs = EC.exportCheck (moduleIdent env) (aliasEnv env)
                              (tyConsEnv env) (valueEnv env) es

-- |Check the export specification
expandExports :: Monad m => Options -> CompEnv Module -> m (CompEnv Module)
expandExports _ (env, Module ps m es is ds)
  = return (env, Module ps m (Just es') is ds)
  where es' = EC.expandExports (moduleIdent env) (aliasEnv env)
                               (tyConsEnv env) (valueEnv env) es

-- |Check for warnings.
warnCheck :: Options -> CompilerEnv -> Module -> [Message]
warnCheck opts env mdl = WC.warnCheck (optWarnOpts opts) (aliasEnv env)
  (valueEnv env) (tyConsEnv env) mdl
