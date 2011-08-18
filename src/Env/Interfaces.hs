module Env.Interfaces where

import qualified Data.Map as Map (Map, empty, lookup)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax (IDecl)

type InterfaceEnv = Map.Map ModuleIdent [IDecl]

lookupInterface :: ModuleIdent -> InterfaceEnv -> Maybe [IDecl]
lookupInterface = Map.lookup

initInterfaceEnv :: InterfaceEnv
initInterfaceEnv = Map.empty
