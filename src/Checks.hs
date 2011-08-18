module Checks where

import Curry.Base.MessageMonad (Message)
import Curry.Syntax

import qualified Check.KindCheck as KC (kindCheck)
import qualified Check.PrecCheck as PC (precCheck)
import qualified Check.SyntaxCheck as SC (syntaxCheck)
import qualified Check.TypeCheck as TC (typeCheck)
import qualified Check.WarnCheck as WC (warnCheck)

import CompilerEnv
import CompilerOpts

kindCheck :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
kindCheck decls env = (decls', env)
  where decls' = KC.kindCheck (moduleIdent env) (tyConsEnv env) decls

precCheck :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
precCheck decls env = (decls', env { opPrecEnv = pEnv' })
  where (pEnv', decls') = PC.precCheck (moduleIdent env) (opPrecEnv env) decls

syntaxCheck :: Options -> [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
syntaxCheck opts decls env = (decls', env)
  where decls' = SC.syntaxCheck withExt (moduleIdent env) (aliasEnv env)
                   (arityEnv env) (valueEnv env) (tyConsEnv env) decls
        withExt = BerndExtension `elem` optExtensions opts

typeCheck :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
typeCheck decls env = (decls, env { tyConsEnv = tcEnv', valueEnv = tyEnv' })
  where (tcEnv', tyEnv') = TC.typeCheck (moduleIdent env)
                              (tyConsEnv env) (valueEnv env) decls

warnCheck :: CompilerEnv -> ([Decl], [Decl]) -> [Message]
warnCheck env = uncurry $ WC.warnCheck (moduleIdent env) (valueEnv env)
