{- |Module aliases

    This module provides an environment for resolving module aliases.

    For example, if a module @M@ is imported via

    @import M as N@

    then @N@ is an alias for @M@, and @M@ is aliased by @N@.

-}
module Env.Import
  ( ImportEnv, initIEnv, fromDeclList, bindAlias, lookupAlias, sureLookupAlias
  ) where

import qualified Data.Map as Map (Map, empty, insert, lookup)
import Data.Maybe (fromMaybe)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax (Decl (..))

type ImportEnv = Map.Map ModuleIdent ModuleIdent

-- |Initial import environment
initIEnv :: ImportEnv
initIEnv = Map.empty

-- |Bind an alias for a module from a single import declaration
bindAlias :: Decl -> ImportEnv -> ImportEnv
bindAlias (ImportDecl _ mid _ alias _)
  = Map.insert mid $ fromMaybe mid alias
bindAlias _ = id -- error "Base.bindAlias: no import declaration"

-- |Create an import environment from a list of import declarations
fromDeclList :: [Decl] -> ImportEnv
fromDeclList = foldr bindAlias initIEnv

-- |
lookupAlias :: ModuleIdent -> ImportEnv -> Maybe ModuleIdent
lookupAlias = Map.lookup

sureLookupAlias :: ModuleIdent -> ImportEnv -> ModuleIdent
sureLookupAlias m = fromMaybe m . lookupAlias m
