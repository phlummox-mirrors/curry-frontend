module CompilerEnv where

import Curry.Base.Ident (ModuleIdent)

import Env.Arity
import Env.Eval
import Env.Interfaces
import Env.Label
import Env.ModuleAliases
import Env.OpPrec
import Env.TypeConstructors
import Env.Value

-- |A compiler environment
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent
  , aliasEnv     :: AliasEnv
  , arityEnv     :: ArityEnv
  , evalAnnotEnv :: EvalEnv
  , interfaceEnv :: InterfaceEnv
  , labelEnv     :: LabelEnv
  , opPrecEnv    :: PEnv
  , tyConsEnv    :: TCEnv
  , valueEnv     :: ValueEnv
  }

initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , aliasEnv     = initAliasEnv
  , arityEnv     = initAEnv
  , evalAnnotEnv = initEEnv
  , interfaceEnv = initInterfaceEnv
  , labelEnv     = initLEnv
  , opPrecEnv    = initPEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  }
