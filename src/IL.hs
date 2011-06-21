{- |IL - Intermediate language

    This module is a simple re-export of the definition of the AST of IL
    and the pretty-printing/xml-priting functions.

    February 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
-}
module IL
  ( module IL.Type
  , ppModule
  , xmlModule
  ) where

import IL.Pretty (ppModule)
import IL.Type
import IL.XML (xmlModule)
