{- |
    Module      :  $Header$
    Description :  Different checks on a Curry module
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
                       2013, Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different checks to be performed on a Curry
    module during compilation, e.g. type checking.
-}
module Checks where

import Curry.Syntax (Module (..), Interface (..))
import Control.Monad.Trans.Either
import Base.Messages

import qualified Checks.InterfaceCheck   as IC (interfaceCheck)
import qualified Checks.ExportCheck      as EC (exportCheck)
import qualified Checks.KindCheck        as KC (kindCheck)
import qualified Checks.PrecCheck        as PC (precCheck)
import qualified Checks.SyntaxCheck      as SC (syntaxCheck)
import qualified Checks.TypeCheck        as TC (typeCheck)
import qualified Checks.WarnCheck        as WC (warnCheck)
import qualified Checks.TypeClassesCheck as TCC (typeClassesCheck)
import qualified Checks.Dictionaries     as DI (insertDicts)

import CompilerEnv
import CompilerOpts

data CheckResult a
  = CheckSuccess a
  | CheckFailed [Message]

instance Monad CheckResult where
  return = CheckSuccess
  (>>=)  = thenCheck

thenCheck :: CheckResult a -> (a -> CheckResult b) -> CheckResult b
thenCheck chk cont = case chk of
  CheckSuccess   a -> cont a
  CheckFailed errs -> CheckFailed errs

interfaceCheck :: CompilerEnv -> Interface -> CheckResult ()
interfaceCheck env intf
  | null errs = return ()
  | otherwise = CheckFailed errs
  where errs = IC.interfaceCheck (opPrecEnv env) (tyConsEnv env)
                                 (valueEnv env) (classEnv env) intf


type Check m = Options -> CompilerEnv -> Module
            -> EitherT [Message] m (CompilerEnv, Module)

-- |Check the kinds of type definitions and signatures.
--
-- * Declarations: Nullary type constructors and type variables are
--                 disambiguated
-- * Environment:  remains unchanged
kindCheck :: Monad m => Check m
kindCheck _ env (Module m es is ds)
  | null msgs = right (env, Module m es is ds')
  | otherwise = left msgs
  where (ds', msgs) = KC.kindCheck (moduleIdent env) (tyConsEnv env) ds

-- |Check for a correct syntax.
--
-- * Declarations: Nullary data constructors and variables are
--                 disambiguated, variables are renamed
-- * Environment:  remains unchanged
syntaxCheck :: Monad m => Check m
syntaxCheck opts env (Module m es is ds)
  | null msgs = right (env, Module m es is ds')
  | otherwise = left msgs
  where (ds', msgs) = SC.syntaxCheck opts (moduleIdent env)
                      (valueEnv env) (tyConsEnv env) (classEnv env) ds

-- |Check the precedences of infix operators.
--
-- * Declarations: Expressions are reordered according to the specified
--                 precedences
-- * Environment:  The operator precedence environment is updated
precCheck :: Monad m => Check m
precCheck _ env (Module m es is ds)
  | null msgs = right (env { opPrecEnv = pEnv' }, Module m es is ds')
  | otherwise = left msgs
  where (ds', pEnv', msgs) = PC.precCheck (moduleIdent env) (opPrecEnv env) ds

-- |Apply the correct typing of the module.
-- Parts of the syntax tree are annotated by their type; the type constructor
-- and value environments are updated.
typeCheck :: Monad m => Bool -> Check m
typeCheck run opts env (Module m es is ds)
  | null msgs = right (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, 
                  (Module m es is newDecls))
  | otherwise = left msgs
  where 
  (tcEnv', tyEnv', newDecls, msgs) 
    = TC.typeCheck (moduleIdent env) (tyConsEnv env) (valueEnv env) 
                   (classEnv env) opts True run ds
                   

-- |Check the export specification
exportCheck :: Monad m => Check m
exportCheck _ env (Module m es is ds)
  | null msgs = right (env, Module m es' is ds)
  | otherwise = left msgs
  where (es', msgs) = EC.exportCheck (moduleIdent env) (aliasEnv env)
                                     (tyConsEnv env) (valueEnv env) 
                                     (classEnv env) es

-- TODO: Which kind of warnings?

-- |Check for warnings.
warnCheck :: CompilerEnv -> Module -> [Message]
warnCheck env mdl = WC.warnCheck (valueEnv env) mdl

-- |Check the type classes
-- Changes the classes environment and removes class and instance declarations, 
-- furthermore adds new code for them
typeClassesCheck :: Monad m => Check m
typeClassesCheck _ env (Module m es is ds) 
  | null msgs = right (env {classEnv = clsEnv}, Module m es is decls') 
  | otherwise = left msgs
  where (decls', clsEnv, msgs) = TCC.typeClassesCheck m ds 
           (classEnv env) (tyConsEnv env) (opPrecEnv env)

-- |Insert dictionaries where necessary. This is actually not a check, but a
-- transformation - but as it can produce errors, it is treated as a check  
insertDicts :: Monad m => Check m
insertDicts opts cEnv m 
  | null msgs = right (cEnv, m')
  | otherwise = left msgs
  where (m', msgs) = DI.insertDicts m cEnv opts
  
