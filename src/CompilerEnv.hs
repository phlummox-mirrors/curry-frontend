{- |
    Module      :  $Header$
    Description :  Environment containing the module's information
    Copyright   :  (c) 2011 - 2013 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines the compilation environment for a single module,
     containing the information needed throughout the compilation process.
-}
module CompilerEnv where

import qualified Data.Map as Map (Map, keys, toList)
import Text.PrettyPrint

import Curry.Base.Ident (ModuleIdent)

import Base.TopEnv (allLocalBindings, allBindings)

import Env.Interface
import Env.ModuleAlias (AliasEnv, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value
import Env.ClassEnv

import CompilerOpts

-- |A compiler environment contains information about the module currently
--  compiled. The information is updated during the different stages of
--  compilation.
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent  -- ^ identifier of the module
  , interfaceEnv :: InterfaceEnv -- ^ declarations of imported interfaces
  , aliasEnv     :: AliasEnv     -- ^ aliases for imported modules
  , tyConsEnv    :: TCEnv        -- ^ type constructors
  , valueEnv     :: ValueEnv     -- ^ functions and data constructors
  , opPrecEnv    :: OpPrecEnv    -- ^ operator precedences
  , classEnv     :: ClassEnv     -- ^ type classes environment
  }

-- |Initial 'CompilerEnv'
initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , interfaceEnv = initInterfaceEnv
  , aliasEnv     = initAliasEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  , opPrecEnv    = initOpPrecEnv
  , classEnv     = initClassEnv
  }


-- |Show the 'CompilerEnv'
showCompilerEnv :: Options -> CompilerEnv -> String
showCompilerEnv opts env = show $ vcat
  [ header "ModuleIdent     " $ textS  $ moduleIdent env
  , header "Interfaces      " $ hcat   $ punctuate comma $ map textS
                                       $ Map.keys $ interfaceEnv env
  , header "ModuleAliases   " $ ppMap  $ aliasEnv     env
  , header "TypeConstructors" $ ppAL (text . show) $ showLocalBindings $ tyConsEnv    env
  , header "Values          " $ ppAL (text . show) $ showLocalBindings $ valueEnv     env
  , header "Precedences     " $ ppAL (text . show) $ showLocalBindings $ opPrecEnv    env
  , header "Classes         " $ ppAL ppClass $ allBindings $ theClasses $ classEnv env
  , header "Instances       " $ vcat (map ppInst (allInstances $ theInstances $ classEnv env))
  , header "ClassMethodsMap " $ ppAL ppClass $ allBindings $ classMethods $ classEnv env
  ]
  where
  header hdr content = hang (text hdr <+> colon) 4 content
  textS = text . show
  showLocalBindings = if optDumpCompleteEnv opts then allBindings else allLocalBindings

-- |Pretty print a 'Map'
ppMap :: (Show a, Show b) => Map.Map a b -> Doc
ppMap = ppAL (text . show) . Map.toList

-- |Pretty print an association list
ppAL :: (Show a, Show b) => (b -> Doc) -> [(a, b)] -> Doc
ppAL pp xs = vcat $ map (\(a,b) -> text (pad a keyWidth) <+> equals <+> b) showXs
  where showXs   = map (\(a,b) -> (show a, pp b)) xs
        keyWidth = maximum (0 : map (length .fst) showXs)
        pad s n  = take n (s ++ repeat ' ')
