{- |
    Module      :  $Header$
    Description :  Environment of imported interfaces
    Copyright   :  (c) 2002-2004, Wolfgang Lux
                       2011, Björn Peemöller   (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides an environment for imported interfaces.
-}
module Env.Interface where

import qualified Data.Map as Map (Map, empty, lookup)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax (IDecl)

type InterfaceEnv = Map.Map ModuleIdent [IDecl]

lookupInterface :: ModuleIdent -> InterfaceEnv -> Maybe [IDecl]
lookupInterface = Map.lookup

initInterfaceEnv :: InterfaceEnv
initInterfaceEnv = Map.empty
