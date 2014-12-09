{- |
    Module      :  $Header$
    Description :  Environment containing the module's information
    Copyright   :  (c) 2011 - 2013 Björn Peemöller
                              2013 Matthias Böhm
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
import Data.Maybe
import Data.List (nub)

import Curry.Base.Ident  (ModuleIdent, preludeMIdent, tcPreludeMIdent, QualIdent (..))
import Curry.Syntax

import Base.TopEnv

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
  { moduleIdent  :: ModuleIdent      -- ^ identifier of the module
  , extensions   :: [KnownExtension] -- ^ enabled language extensions
  , interfaceEnv :: InterfaceEnv     -- ^ declarations of imported interfaces
  , aliasEnv     :: AliasEnv         -- ^ aliases for imported modules
  , tyConsEnv    :: TCEnv            -- ^ type constructors
  , valueEnv     :: ValueEnv         -- ^ functions and data constructors
  , opPrecEnv    :: OpPrecEnv        -- ^ operator precedences
  , classEnv     :: ClassEnv     -- ^ type classes environment
  }

-- |Initial 'CompilerEnv'
initCompilerEnv :: ModuleIdent -> CompilerEnv
initCompilerEnv mid = CompilerEnv
  { moduleIdent  = mid
  , extensions   = []
  , interfaceEnv = initInterfaceEnv
  , aliasEnv     = initAliasEnv
  , tyConsEnv    = initTCEnv
  , valueEnv     = initDCEnv
  , opPrecEnv    = initOpPrecEnv
  , classEnv     = initClassEnv
  }


-- |Show the 'CompilerEnv'
showCompilerEnv :: DebugOpts -> CompilerEnv -> String
showCompilerEnv opts env = show $ vcat
  [ header "ModuleIdent       " $ textS $ moduleIdent env
  , header "Language Etensions" $ text  $ show $ extensions  env
  , header "Interfaces        " $ hcat  $ punctuate comma $ map textS
                                        $ Map.keys $ interfaceEnv env
  , header "ModuleAliases     " $ ppMap $ aliasEnv     env
  , header "TypeConstructors  " $ ppAL (text . show) $ allLocalBindings $ tyConsEnv env
  , header "Values            " $ ppAL (text . show) $ allLocalBindings $ valueEnv  env
  , header "Precedences       " $ ppAL (text . show) $ allLocalBindings $ opPrecEnv env
  , header "Classes         " $ ppAL ppClass $ showLocalBindings $ theClasses $ classEnv env
  , header "Instances       " $ vcat (map ppInst (filter filterInst $ allInstances $ theInstances $ classEnv env))
  -- , header "ClassMethodsMap " $ ppAL ppClass $ showLocalBindings $ classMethods $ classEnv env
  , header "CanonClassMap   " $ ppAL ppClass $ filter filterCanon $ Map.toList $ canonClassMap $ classEnv env
  ]
  where
  header hdr content = hang (text hdr <+> colon) 4 content
  textS = text . show
  showLocalBindings :: (Entity a, Eq a) => TopEnv a -> [(QualIdent, a)]
  showLocalBindings = 
    if showAll
    then allBindings
    else -- show only bindings that are outside the prelude
      nub . map (\(x, _, y) -> (x, y)) . 
        filter (\(_, origName', _) -> isNothing (qidModule origName') || 
            (fromJust (qidModule origName') /= preludeMIdent
          && fromJust (qidModule origName') /= tcPreludeMIdent)) . 
        allBindingsWithOrigNames
  filterInst :: Instance -> Bool
  filterInst (Instance { origin = o }) = 
    if showAll then True else o /= tcPreludeMIdent 
  filterCanon :: (QualIdent, Class) -> Bool
  filterCanon (qid, _) = if showAll then True
    else isNothing (qidModule qid) || (fromJust (qidModule qid)) /= tcPreludeMIdent 
  showAll = dbDumpCompleteEnv opts

-- |Pretty print a 'Map'
ppMap :: (Show a, Show b) => Map.Map a b -> Doc
ppMap = ppAL (text . show) . Map.toList

-- |Pretty print an association list
ppAL :: (Show a, Show b) => (b -> Doc) -> [(a, b)] -> Doc
ppAL pp xs = vcat $ map (\(a,b) -> text (pad a keyWidth) <+> equals <+> b) showXs
  where showXs   = map (\(a,b) -> (show a, pp b)) xs
        keyWidth = maximum (0 : map (length .fst) showXs)
        pad s n  = take n (s ++ repeat ' ')
