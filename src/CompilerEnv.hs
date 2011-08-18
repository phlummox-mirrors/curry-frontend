module CompilerEnv where

import Curry.Base.Ident (ModuleIdent)

import Env.Arity
import Env.Eval
import Env.Import
import Env.Interfaces
import Env.Label
import Env.OpPrec
import Env.TypeConstructors
import Env.Value

-- |A compiler environment
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent
  , arityEnv     :: ArityEnv
  , evalAnnotEnv :: EvalEnv
  , importEnv    :: ImportEnv
  , interfaceEnv :: InterfaceEnv
  , labelEnv     :: LabelEnv
  , opPrecEnv    :: PEnv
  , tyConsEnv    :: TCEnv
  , valueEnv     :: ValueEnv
  }

initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , arityEnv     = initAEnv
  , evalAnnotEnv = initEEnv
  , importEnv    = initIEnv
  , interfaceEnv = initInterfaceEnv
  , labelEnv     = initLEnv
  , opPrecEnv    = initPEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  }
