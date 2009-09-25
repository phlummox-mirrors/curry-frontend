{-
  A simple interface for reading and manipulating Curry
  source code.

  (c) 2009, Holger Siegel.
-}

module Curry.Syntax(module Curry.Syntax.Type,
                   parseModule, parseHeader
                   ) where

import Control.Monad
import Data.List

import Curry.Base.MessageMonad
import Curry.Syntax.Type

import qualified Curry.Syntax.Parser as CSP

import Curry.Syntax.Unlit



parseModule :: Bool -> FilePath -> String -> MsgMonad Module
parseModule likeFlat fn =
  unlitLiterate fn >=> CSP.parseSource likeFlat fn


parseHeader :: FilePath -> String -> MsgMonad Module
parseHeader fn =
  unlitLiterate fn >=> CSP.parseHeader fn

-- Literate source files use the extension ".lcurry"
unlitLiterate :: FilePath -> String -> MsgMonad String
unlitLiterate fn s
  | isLiterateSource fn = unlit fn s
  | otherwise = return s

isLiterateSource :: FilePath -> Bool
isLiterateSource fn = litExt `isSuffixOf` fn

litExt = ".lcurry"

