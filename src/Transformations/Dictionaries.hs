{- |
    Module      :  $Header$
    Description :  
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The main function of this module transforms the abstract syntax tree by
    adding dictionary parameters where necessary. 
-}

module Transformations.Dictionaries (insertDicts) where

import CompilerEnv
import Curry.Syntax
import Env.ClassEnv

import Control.Monad.State as S

-- ----------------------------------------------------------------------------
-- the state monad used
-- ----------------------------------------------------------------------------

type DI = S.State DIState

data DIState = DIState 
  { theClassEnv :: ClassEnv
  }

initState :: ClassEnv -> DIState
initState cEnv = DIState cEnv

runDI :: DI a -> DIState -> a
runDI comp init0 = let (a, _s) = S.runState comp init0 in a

getClassEnv :: DI ClassEnv
getClassEnv = S.gets theClassEnv

-- ----------------------------------------------------------------------------
-- the transformation functions
-- ----------------------------------------------------------------------------

-- |The main function of this module. It descends into the syntax tree and
-- inserts dictionary parameters (in function declarations and in expressions)
insertDicts :: Module -> CompilerEnv -> Module
insertDicts mdl cEnv = 
  runDI (diModule mdl) (initState $ classEnv cEnv)   

-- |convert a whole module
diModule :: Module -> DI Module
diModule (Module m e i ds) = return $ Module m e i ds

