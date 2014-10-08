{- |
    Module      :  $Header$
    Description :  Intermediate language
    Copyright   :  (c) 2014, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module is a simple re-export of the definition of the AST of IL
    and the pretty-printing of IL modules.
-}
module IL ( module IL.Type, ppModule ) where

import IL.Pretty (ppModule)
import IL.Type
