{- |
    Module      :  $Header$
    Description :  Checks deriving clauses
    Copyright   :  (c)        2016 Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   TODO
-}
module Checks.DeriveCheck (deriveCheck) where

import Curry.Syntax

import Base.Messages (Message)

deriveCheck :: Module a -> [Message]
deriveCheck _ = []
