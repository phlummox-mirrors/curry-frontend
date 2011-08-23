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
kindCheck :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
kindCheck decls env = (decls', env)
  where decls' = KC.kindCheck (moduleIdent env) (tyConsEnv env) decls

-- |Apply the precendences of infix operators.
-- This function reanrranges the AST.
precCheck :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
precCheck decls env = (decls', env { opPrecEnv = pEnv' })
  where (pEnv', decls') = PC.precCheck (moduleIdent env) (opPrecEnv env) decls

-- |Apply the syntax check.
syntaxCheck :: Options -> [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
syntaxCheck opts decls env = (decls', env)
  where decls' = SC.syntaxCheck withExt (moduleIdent env) (aliasEnv env)
                   (arityEnv env) (valueEnv env) (tyConsEnv env) decls
        withExt = BerndExtension `elem` optExtensions opts

-- |Apply the type check.
typeCheck :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
typeCheck decls env = (decls, env { tyConsEnv = tcEnv', valueEnv = tyEnv' })
  where (tcEnv', tyEnv') = TC.typeCheck (moduleIdent env)
                              (tyConsEnv env) (valueEnv env) decls

-- TODO: Which one?

-- |Check for warnings.
warnCheck :: CompilerEnv -> ([Decl], [Decl]) -> [Message]
warnCheck env = uncurry $ WC.warnCheck (moduleIdent env) (valueEnv env)
