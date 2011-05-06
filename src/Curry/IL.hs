{- |IL - Intermediate language

    This module is a simple re-export of the definition of the AST of IL
    and the pretty-printing/xml-priting functions.

    February 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
-}
module Curry.IL
  ( module Curry.IL.Type
  , ppModule
  , xmlModule
  ) where

import Curry.IL.Pretty (ppModule)
import Curry.IL.Type
import Curry.IL.XML (xmlModule)
