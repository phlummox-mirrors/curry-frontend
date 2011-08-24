{- |
    Module      :  $Header$
    Description :  Code transformations
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module subsumes the different transformations of the source code.
-}
module Transformations where

import Curry.Syntax

import Base.Types

import Transformations.CaseCompletion as CC (completeCase)
import Transformations.CurryToIL      as IL (ilTrans, translType)
import Transformations.Desugar        as DS (desugar)
import Transformations.Lift           as L  (lift)
import Transformations.Qual           as Q  (qual)
import Transformations.Simplify       as S  (simplify)

import CompilerEnv
import qualified IL

-- |Add missing case branches
completeCase :: IL.Module -> CompilerEnv -> (IL.Module, CompilerEnv)
completeCase mdl env = (CC.completeCase (interfaceEnv env) mdl, env)

-- |Translate into the intermediate language
ilTrans :: Bool -> Module -> CompilerEnv -> (IL.Module, CompilerEnv)
ilTrans flat mdl env = (il, env)
  where il = IL.ilTrans flat (valueEnv env) (tyConsEnv env) (evalAnnotEnv env) mdl

-- |Translate a type into its representation in the intermediate language
translType :: Type -> IL.Type
translType = IL.translType

-- |Remove syntactic sugar
desugar :: Module -> CompilerEnv -> (Module, CompilerEnv)
desugar mdl env = (mdl', env { valueEnv = tyEnv' })
  where (mdl', tyEnv') = DS.desugar (valueEnv env) (tyConsEnv env) mdl

-- |Lift local declarations
lift :: Module -> CompilerEnv -> (Module, CompilerEnv)
lift mdl env = (mdl', env { valueEnv = tyEnv', evalAnnotEnv = eEnv', arityEnv = aEnv' })
  where (mdl', tyEnv', eEnv', aEnv')
           = L.lift (valueEnv env) (evalAnnotEnv env) (arityEnv env) mdl

-- |Fully qualify used constructors and functions
qual :: Module -> CompilerEnv -> (Module, CompilerEnv)
qual (Module m es is ds) env = (Module m es is ds', env)
  where ds' = Q.qual (moduleIdent env) (valueEnv env) ds

-- |Simplify the source code
simplify :: Bool -> Module -> CompilerEnv -> (Module, CompilerEnv)
simplify flat mdl env = (mdl', env { valueEnv = tyEnv' })
  where (mdl', tyEnv') = S.simplify flat (valueEnv env) (evalAnnotEnv env) mdl
