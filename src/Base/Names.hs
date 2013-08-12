{- |
    Module      :  $Header$
    Description :  Provides internal names used in transformations 
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
    
    This module exports name generation functions, e.g. for dictionary selector
    functions and for internal function names in connection with instances
-}

module Base.Names 
  (
    -- * the separator string
    sep
    -- * prefixes for constructed identifiers
  , implPrefix, dictTypePrefix, identPrefix, defPrefix
    -- * name generation functions
  , mkSelFunName, mkDictName, mkDictTypeName, mkDefFunName
    -- * functions that test whether an identifier is a constructed identifier
    -- of a given type
  , isDictType, isDictionary, isSelFun, isDefaultMethod 
  ) where

import Data.List

-- | prefix that indicates that the identifier is constructed by the compiler
import Curry.Base.Ident (identPrefix, sep, Ident)

-- |The prefix for dictionary types
dictTypePrefix :: String
dictTypePrefix = "Dict" ++ sep

-- |The prefix for dictionaries
dictPrefix :: String
dictPrefix = "dict" ++ sep

-- |The prefix for selector functions
selFunPrefix :: String
selFunPrefix = "sel" ++ sep

-- |The prefix for functions that are implemented in a given instance declaration
implPrefix :: String
implPrefix = "impl" ++ sep

-- |The prefix for default methods
defPrefix :: String
defPrefix = "def" ++ sep

-- |creates a name for a selection function 
mkSelFunName :: String -> String -> String
mkSelFunName cls what = 
  selFunPrefix ++ cls ++ sep ++ what
  
-- |create a name for a dictionary
mkDictName :: String -> String -> String
mkDictName cls ty = dictPrefix ++ cls ++ sep ++ ty

-- |creates a name for a dictionary type
mkDictTypeName :: String -> String
mkDictTypeName cls = dictTypePrefix ++ cls

mkDefFunName :: String -> String -> String
mkDefFunName cls fun0 = defPrefix ++ cls ++ sep ++ fun0

isDictType :: Ident -> Bool
isDictType i = dictTypePrefix `isPrefixOf` show i

isDictionary :: Ident -> Bool
isDictionary i = dictPrefix `isPrefixOf` show i

isSelFun :: Ident -> Bool
isSelFun i = selFunPrefix `isPrefixOf` show i

isDefaultMethod :: Ident -> Bool
isDefaultMethod i = defPrefix `isPrefixOf` show i

