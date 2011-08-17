module CompilerEnv where

import Curry.Base.Ident (ModuleIdent)

import Env.Arity
import Env.Eval
import Env.Import
import Env.Label
import Env.Module
import Env.OpPrec
import Env.TypeConstructors
import Env.Value

-- |A compiler environment
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent
  , arityEnv     :: ArityEnv
  , evalAnnotEnv :: EvalEnv
  , importEnv    :: ImportEnv
  , labelEnv     :: LabelEnv
  , moduleEnv    :: ModuleEnv
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
  , labelEnv     = initLEnv
  , moduleEnv    = initMEnv
  , opPrecEnv    = initPEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  }
