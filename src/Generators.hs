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

import qualified Curry.AbstractCurry         as AC (CurryProg)
import qualified Curry.ExtendedFlat.Type     as EF (Prog)
import qualified Curry.Syntax                as CS (Module)

import qualified Generators.GenAbstractCurry as GAC
import qualified Generators.GenFlatCurry     as GFC

import CompilerEnv
import IL (Module)
import ModuleSummary

-- |Generate typed AbstractCurry
genTypedAbstractCurry :: CompilerEnv -> CS.Module a -> AC.CurryProg
genTypedAbstractCurry = GAC.genAbstractCurry False

-- |Generate untyped AbstractCurry
genUntypedAbstractCurry :: CompilerEnv -> CS.Module a -> AC.CurryProg
genUntypedAbstractCurry = GAC.genAbstractCurry True

-- |Generate FlatCurry
genFlatCurry :: ModuleSummary -> CompilerEnv -> IL.Module -> EF.Prog
genFlatCurry ms env = GFC.genFlatCurry ms
  (interfaceEnv env) (valueEnv env) (tyConsEnv env)

-- |Generate a FlatCurry interface
genFlatInterface :: ModuleSummary -> CompilerEnv -> IL.Module -> EF.Prog
genFlatInterface ms env = GFC.genFlatInterface ms
  (interfaceEnv env) (valueEnv env) (tyConsEnv env)
