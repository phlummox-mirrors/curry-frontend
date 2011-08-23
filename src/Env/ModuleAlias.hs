{- |
    Module      :  $Header$
    Description :  Environment of module aliases
    Copyright   :  (c) 2002-2004, Wolfgang Lux
                       2011, Björn Peemöller   (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides an environment for resolving module aliases.

    For example, if a module @M@ is imported via

    @import M as N@

    then @N@ is an alias for @M@, and @M@ is aliased by @N@.
-}
module Env.ModuleAlias
  ( AliasEnv, initAliasEnv, importAliases
  , bindAlias, lookupAlias, sureLookupAlias
  ) where

import qualified Data.Map as Map (Map, empty, findWithDefault, insert, lookup)
import Data.Maybe (fromMaybe)

import Curry.Base.Ident (ModuleIdent)
import Curry.Syntax (Decl (..))

type AliasEnv = Map.Map ModuleIdent ModuleIdent

-- |Initial alias environment
initAliasEnv :: AliasEnv
initAliasEnv = Map.empty

-- |Create an alias environment from a list of import declarations
importAliases :: [Decl] -> AliasEnv
importAliases = foldr bindAlias initAliasEnv

-- |Bind an alias for a module from a single import declaration
bindAlias :: Decl -> AliasEnv -> AliasEnv
bindAlias (ImportDecl _ mid _ alias _) = Map.insert mid $ fromMaybe mid alias
bindAlias _ = id

-- |Lookup the alias for a module, if existent
lookupAlias :: ModuleIdent -> AliasEnv -> Maybe ModuleIdent
lookupAlias = Map.lookup

-- |Try to lookup the alias for a module and default to the module if missing
sureLookupAlias :: ModuleIdent -> AliasEnv -> ModuleIdent
sureLookupAlias m = Map.findWithDefault m m
