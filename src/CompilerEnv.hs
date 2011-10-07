{- |
    Module      :  $Header$
    Description :  Environment containing the module's information
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines an environment for a module containing the information
    needed throughout the compilation of the module.
-}
module CompilerEnv where

import Curry.Base.Ident (ModuleIdent)

import Env.Eval
import Env.Interface
import Env.ModuleAlias
import Env.OpPrec
import Env.TypeConstructors
import Env.Value

-- |A compiler environment contains information about the module currently
--  compiled. The information is updated during the different stages of
--  compilation.
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent  -- ^ identifier of the module
  , aliasEnv     :: AliasEnv     -- ^ aliases for imported modules
  , evalAnnotEnv :: EvalEnv      -- ^ evaluation annotations
  , interfaceEnv :: InterfaceEnv -- ^ declarations of imported interfaces
  , opPrecEnv    :: PEnv         -- ^ operator precedences
  , tyConsEnv    :: TCEnv        -- ^ type constructors
  , valueEnv     :: ValueEnv     -- ^ functions and data constructors
  } deriving Show

initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , aliasEnv     = initAliasEnv
  , evalAnnotEnv = initEEnv
  , interfaceEnv = initInterfaceEnv
  , opPrecEnv    = initPEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  }
