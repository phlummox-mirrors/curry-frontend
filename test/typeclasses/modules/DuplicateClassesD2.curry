
module DuplicateClassesD2 (D(..), C(..)) where

import DuplicateClassesD1

class C a where
  funC2 :: a -> a -> Bool
  
