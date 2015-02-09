{- |
    Module      :  $Header$
    Description :  Different checks on a Curry module
    Copyright   :  (c) 2011 - 2013, Björn Peemöller
                              2013, Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different checks to be performed on a Curry
    module during compilation, e.g. type checking.
-}
module Checks where

import qualified Checks.InterfaceCheck   as IC (interfaceCheck)
import qualified Checks.ExportCheck      as EC (exportCheck)
import qualified Checks.KindCheck        as KC (kindCheck)
import qualified Checks.PrecCheck        as PC (precCheck)
import qualified Checks.SyntaxCheck      as SC (syntaxCheck)
import qualified Checks.TypeCheck        as TC (typeCheck)
import qualified Checks.WarnCheck        as WC (warnCheck)
import qualified Checks.TypeClassesCheck as TCC (typeClassesCheck)
import qualified Checks.Dictionaries     as DI (insertDicts)

import Curry.Base.Monad
import Curry.Syntax (Module (..), Interface (..))

import Base.Messages
import CompilerEnv
import CompilerOpts

type Check m a = Options -> CompEnv a -> CYT m (CompEnv a)

interfaceCheck :: Monad m => Check m Interface
interfaceCheck _ (env, intf)
  | null msgs = ok (env, intf)
  | otherwise = failMessages msgs
  where msgs = IC.interfaceCheck (opPrecEnv env) (tyConsEnv env)
                                 (valueEnv env) (classEnv env) intf

-- |Check the kinds of type definitions and signatures.
--
-- * Declarations: Nullary type constructors and type variables are
--                 disambiguated
-- * Environment:  remains unchanged
kindCheck :: Monad m => Check m Module
kindCheck _ (env, mdl)
  | null msgs = ok (env, mdl')
  | otherwise = failMessages msgs
  where (mdl', msgs) = KC.kindCheck (tyConsEnv env) mdl

-- |Check for a correct syntax.
--
-- * Declarations: Nullary data constructors and variables are
--                 disambiguated, variables are renamed
-- * Environment:  remains unchanged
syntaxCheck :: Monad m => Check m Module
syntaxCheck opts (env, mdl)
  | null msgs = ok (env { extensions = exts }, mdl')
  | otherwise = failMessages msgs
  where ((mdl', exts), msgs) = SC.syntaxCheck opts
                      (valueEnv env) (tyConsEnv env) (classEnv env) mdl

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
-- Parts of the syntax tree are annotated by their type; the type constructor
-- and value environments are updated.
typeCheck :: Monad m => Bool -> Check m Module
typeCheck run opts (env,Module recFlag m es is ds)
  | null msgs = ok (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }
                   , Module recFlag m es is newDecls)
  | otherwise = failMessages msgs
  where 
  (tcEnv', tyEnv', newDecls, msgs) = 
    TC.typeCheck (moduleIdent env) (tyConsEnv env) (valueEnv env) 
                 (classEnv env) opts True run ds

-- |Check the export specification
exportCheck :: Monad m => Check m Module
exportCheck _ (env, Module ps m es is ds)
  | null msgs = ok (env, Module ps m es' is ds)
  | otherwise = failMessages msgs
  where (es', msgs) = EC.exportCheck (moduleIdent env) (aliasEnv env)
                                     (tyConsEnv env) (valueEnv env) 
                                     (classEnv env) es

-- |Check for warnings.
warnCheck :: Options -> CompEnv Module -> [Message]
warnCheck opts (env,mdl) = WC.warnCheck (optWarnOpts opts)
                                        (aliasEnv env)
                                        (valueEnv env)
                                        (tyConsEnv env)
                                        mdl

-- |Check the type classes
-- Changes the classes environment and removes class and instance declarations, 
-- furthermore adds new code for them
typeClassesCheck :: Monad m => Check m Module
typeClassesCheck opts (env,Module recFlag m es is ds)
  | null msgs = ok (env {classEnv = clsEnv}, Module recFlag m es is decls') 
  | otherwise = failMessages msgs
 where
  (decls', clsEnv, msgs) = TCC.typeClassesCheck m opts ds 
           (classEnv env) (tyConsEnv env) (opPrecEnv env)

-- |Insert dictionaries where necessary. This is actually not a check, but a
-- transformation - but as it can produce errors, it is treated as a check  
insertDicts :: Monad m => Check m Module
insertDicts opts (cEnv,mdl) 
  | null msgs = ok (cEnv, mdl')
  | otherwise = failMessages msgs
  where (mdl', msgs) = DI.insertDicts mdl cEnv opts
  

