{- |
    Module      :  $Header$
    Description :  Intermediate language
    Copyright   :  (c) 2011, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module is a simple re-export of the definition of the AST of IL
    and the pretty-printing/xml-printing functions.
-}
module IL
  ( module IL.Type
  , ppModule
  , xmlModule
  ) where

import IL.Pretty (ppModule)
import IL.Type
import IL.XML    (xmlModule)
