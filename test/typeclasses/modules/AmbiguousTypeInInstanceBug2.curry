

module AmbiguousTypeInInstanceBug2 where

import AmbiguousTypeInInstanceBug1

data T a = T a

class C a where
  funC :: a -> a

instance C (T a) where
  funC x = x



