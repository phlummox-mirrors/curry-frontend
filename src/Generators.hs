{- |
    Module      :  $Header$
    Description :  Code generators
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different code generators.
-}
module Generators where

import Curry.Base.Message (Message)

import qualified Curry.AbstractCurry as AC (CurryProg)
import qualified Curry.ExtendedFlat.Type as EF (Prog)
import qualified Curry.Syntax as CS (Module)

import qualified Generators.GenAbstractCurry as GAC
import qualified Generators.GenFlatCurry     as GFC

import CompilerEnv
import CompilerOpts
import IL (Module)
import ModuleSummary

-- |Generate AbstractCurry
genTypedAbstractCurry :: CompilerEnv -> CS.Module -> AC.CurryProg
genTypedAbstractCurry = GAC.genTypedAbstract

-- |Generate untyped AbstractCurry
genUntypedAbstractCurry :: CompilerEnv -> CS.Module -> AC.CurryProg
genUntypedAbstractCurry = GAC.genUntypedAbstract

-- |Generate FlatCurry
genFlatCurry :: Options -> ModuleSummary -> CompilerEnv -> IL.Module
             -> (EF.Prog, [Message])
genFlatCurry opts ms env = GFC.genFlatCurry opts ms
  (interfaceEnv env) (valueEnv env) (tyConsEnv env)

-- |Generate a FlatCurry interface
genFlatInterface :: Options -> ModuleSummary -> CompilerEnv -> IL.Module
                 -> (EF.Prog, [Message])
genFlatInterface opts ms env = GFC.genFlatInterface opts ms
  (interfaceEnv env) (valueEnv env) (tyConsEnv env) (classEnv env)
