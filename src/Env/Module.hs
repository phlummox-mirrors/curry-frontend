module Env.Module where

import qualified Data.Map as Map (Map, empty, lookup)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax (IDecl)

type ModuleEnv = Map.Map ModuleIdent [IDecl]

lookupModule :: ModuleIdent -> ModuleEnv -> Maybe [IDecl]
lookupModule = Map.lookup

initMEnv :: ModuleEnv
initMEnv = Map.empty
