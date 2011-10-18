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

import qualified Data.Map as Map (keys)

import Curry.Base.Ident (ModuleIdent)

import Base.TopEnv (localBindings)

import Env.Eval
import Env.Interface
import Env.ModuleAlias
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

-- |A compiler environment contains information about the module currently
--  compiled. The information is updated during the different stages of
--  compilation.
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent  -- ^ identifier of the module
  , interfaceEnv :: InterfaceEnv -- ^ declarations of imported interfaces
  , aliasEnv     :: AliasEnv     -- ^ aliases for imported modules
  , tyConsEnv    :: TCEnv        -- ^ type constructors
  , valueEnv     :: ValueEnv     -- ^ functions and data constructors
  , opPrecEnv    :: PEnv         -- ^ operator precedences
  , evalAnnotEnv :: EvalEnv      -- ^ evaluation annotations
  }

initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , interfaceEnv = initInterfaceEnv
  , aliasEnv     = initAliasEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  , opPrecEnv    = initPEnv
  , evalAnnotEnv = initEEnv
  }

showCompilerEnv :: CompilerEnv -> String
showCompilerEnv env = unlines $ concat
  [ header "ModuleIdent"      $ show $ moduleIdent  env
  , header "Interfaces"       $ show $ Map.keys      $ interfaceEnv env
  , header "ModuleAliases"    $ show $ aliasEnv     env
  , header "TypeConstructors" $ show $ localBindings $ tyConsEnv env
  , header "Values"           $ show $ localBindings $ valueEnv  env
  , header "Precedences"      $ show $ localBindings $ opPrecEnv env
  , header "Eval Annotations" $ show $ evalAnnotEnv env
  ]
  where header hdr content = [hdr, replicate (length hdr) '=', content]