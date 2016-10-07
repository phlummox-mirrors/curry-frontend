{- |
  Module      :  $Header$
  Description :  Deriving instances
  Copyright   :  (c) 2016        Finn Teegen
  License     :  OtherLicense

  Maintainer  :  bjp@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  TODO
-}
module Transformations.Derive (derive) where

import Curry.Syntax

import Base.Types

-- Note: The methods and arities of the generated instance declarations have to
-- correspond to the methods and arities entered previously into the instance
-- environment (see instance check).

derive :: Module PredType -> Module PredType
derive = id
