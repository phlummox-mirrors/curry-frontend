{- |
    Module      :  $Header$
    Description :  Custom Show implementation for IL
    Copyright   :  (c) 2015 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements a generic show function comparable to the one
   obtained by @deriving Show@. However, the internal representation of
   identifiers is hidden to avoid syntactic clutter.
-}

module IL.ShowModule (showModule) where

import Data.Char     (ord)
import Data.Generics (Data, extQ, ext1Q, ext2Q, gmapQ, toConstr, showConstr)
import Data.List     (intersperse)

import Curry.Base.Ident
import IL.Type

showModule :: Module -> String
showModule m = gshowsPrec m []

gshowsPrec :: Data a => a -> ShowS
gshowsPrec
  =       genericShowsPrec
  `ext1Q` showsList
  `ext2Q` showsTuple
  `extQ`  (shows :: String -> ShowS)
  `extQ`  showsEscape
  `extQ`  showsModuleIdent
  `extQ`  showsIdent
  `extQ`  showsQualIdent
  where

  genericShowsPrec :: Data a => a -> ShowS
  genericShowsPrec t
    = showParen (not (null args))
    $ showString (showConstr (toConstr t))
    . (if null args then id else showChar ' ')
    . foldr (.) id args
    where args = intersperse (showChar ' ') (gmapQ gshowsPrec t)

  showsList :: Data a => [a] -> ShowS
  showsList xs = showChar '['
               . foldr (.) (showChar ']')
                           (intersperse (showChar ',') (map gshowsPrec xs))

  showsTuple :: (Data a, Data b) => (a, b) -> ShowS
  showsTuple (x, y)
    = showChar '(' . gshowsPrec x . showChar ',' . gshowsPrec y . showChar ')'

  showsEscape :: Char -> ShowS
  showsEscape c
    | o <   10  = showString "'\\00" . shows o . showChar '\''
    | o <   32  = showString "'\\0"  . shows o . showChar '\''
    | o == 127  = showString "'\\127'"
    | otherwise = shows c
    where o = ord c

  showsModuleIdent :: ModuleIdent -> ShowS
  showsModuleIdent m = showString (moduleName m)

  showsIdent :: Ident -> ShowS
  showsIdent i = showString (showIdent i)

  showsQualIdent :: QualIdent -> ShowS
  showsQualIdent q = showString (qualName q)
