{- |
    Module      :  $Header$
    Description :  Environment containing the module's information
    Copyright   :  (c) 2011 - 2015 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines the compilation environment for a single module,
     containing the information needed throughout the compilation process.
-}
module CompilerEnv where

import qualified Data.Map as Map (Map, keys, toList)

import Curry.Base.Ident  (ModuleIdent)
import Curry.Base.Pretty
import Curry.Base.Span   (Span)
import Curry.Syntax

import Base.TopEnv (allLocalBindings)

import Env.Interface
import Env.ModuleAlias (AliasEnv, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

type CompEnv a = (CompilerEnv, a)

-- |A compiler environment contains information about the module currently
--  compiled. The information is updated during the different stages of
--  compilation.
data CompilerEnv = CompilerEnv
  { moduleIdent  :: ModuleIdent         -- ^ identifier of the module
  , filePath     :: FilePath            -- ^ 'FilePath' of compilation target
  , extensions   :: [KnownExtension]    -- ^ enabled language extensions
  , tokens       :: [(Span, Token)]     -- ^ token list of module
  , interfaceEnv :: InterfaceEnv        -- ^ declarations of imported interfaces
  , aliasEnv     :: AliasEnv            -- ^ aliases for imported modules
  , tyConsEnv    :: TCEnv               -- ^ type constructors
  , valueEnv     :: ValueEnv            -- ^ functions and data constructors
  , opPrecEnv    :: OpPrecEnv           -- ^ operator precedences
  }

-- |Initial 'CompilerEnv'
initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , filePath     = []
  , extensions   = []
  , tokens       = []
  , interfaceEnv = initInterfaceEnv
  , aliasEnv     = initAliasEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  , opPrecEnv    = initOpPrecEnv
  }

-- |Show the 'CompilerEnv'
showCompilerEnv :: CompilerEnv -> String
showCompilerEnv env = show $ vcat
  [ header "Module Identifier  " $ textS $ moduleIdent env
  , header "FilePath"            $ text  $ filePath    env
  , header "Language Extensions" $ text  $ show $ extensions  env
  , header "Interfaces         " $ hcat  $ punctuate comma $ map textS
                                         $ Map.keys $ interfaceEnv env
  , header "Module Aliases     " $ ppMap $ aliasEnv     env
  , header "Precedences        " $ ppAL $ allLocalBindings $ opPrecEnv env
  , header "Type Constructors  " $ ppAL $ allLocalBindings $ tyConsEnv env
  , header "Values             " $ ppAL $ allLocalBindings $ valueEnv  env
  ]
  where
  header hdr content = hang (text hdr <+> colon) 4 content
  textS = text . show

-- |Pretty print a 'Map'
ppMap :: (Show a, Show b) => Map.Map a b -> Doc
ppMap = ppAL . Map.toList

-- |Pretty print an association list
ppAL :: (Show a, Show b) => [(a, b)] -> Doc
ppAL xs = vcat
        $ map (\(a,b) -> text (pad a keyWidth) <+> equals <+> text b) showXs
  where showXs   = map (\(a,b) -> (show a, show b)) xs
        keyWidth = maximum (0 : map (length .fst) showXs)
        pad s n  = take n (s ++ repeat ' ')
