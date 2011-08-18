{- |Module aliases

    This module provides an environment for resolving module aliases.

    For example, if a module @M@ is imported via

    @import M as N@

    then @N@ is an alias for @M@, and @M@ is aliased by @N@.

-}
module Env.ModuleAliases
  ( AliasEnv, initAliasEnv, fromImportDecls
  , bindAlias, lookupAlias, sureLookupAlias
  ) where

import qualified Data.Map as Map (Map, empty, insert, lookup)
import Data.Maybe (fromMaybe)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax (Decl (..))

type AliasEnv = Map.Map ModuleIdent ModuleIdent

-- |Initial alias environment
initAliasEnv :: AliasEnv
initAliasEnv = Map.empty

-- |Create an alias environment from a list of import declarations
fromImportDecls :: [Decl] -> AliasEnv
fromImportDecls = foldr bindAlias initAliasEnv

-- |Bind an alias for a module from a single import declaration
bindAlias :: Decl -> AliasEnv -> AliasEnv
bindAlias (ImportDecl _ mid _ alias _) = Map.insert mid $ fromMaybe mid alias
bindAlias _ = id

-- |
lookupAlias :: ModuleIdent -> AliasEnv -> Maybe ModuleIdent
lookupAlias = Map.lookup

sureLookupAlias :: ModuleIdent -> AliasEnv -> ModuleIdent
sureLookupAlias m = fromMaybe m . lookupAlias m
