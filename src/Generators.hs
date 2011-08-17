module Generators where

import Curry.Base.MessageMonad (Message)

import qualified Curry.AbstractCurry as AC (CurryProg)
import qualified Curry.ExtendedFlat.Type as EF (Prog)
import qualified Curry.Syntax as CS (Module)

import qualified Gen.GenAbstractCurry as GAC
import qualified Gen.GenFlatCurry as GFC

import CompilerEnv
import CompilerOpts
import IL
import ModuleSummary

genTypedAbstractCurry :: CompilerEnv -> CS.Module -> AC.CurryProg
genTypedAbstractCurry env
   = GAC.genTypedAbstract (valueEnv env) (tyConsEnv env)

genUntypedAbstractCurry :: CompilerEnv -> CS.Module -> AC.CurryProg
genUntypedAbstractCurry env
   = GAC.genUntypedAbstract (valueEnv env) (tyConsEnv env)

genFlatCurry :: Options -> ModuleSummary -> CompilerEnv -> IL.Module
             -> (EF.Prog, [Message])
genFlatCurry opts ms env
  = GFC.genFlatCurry opts ms (moduleEnv env) (valueEnv env) (tyConsEnv env) (arityEnv env)

genFlatInterface :: Options -> ModuleSummary -> CompilerEnv -> IL.Module
                 -> (EF.Prog, [Message])
genFlatInterface opts ms env
  = GFC.genFlatInterface opts ms (moduleEnv env) (valueEnv env) (tyConsEnv env) (arityEnv env)
