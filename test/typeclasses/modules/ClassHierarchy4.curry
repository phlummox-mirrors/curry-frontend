
module ClassHierarchy4 where

import ClassHierarchy3

class E2 a where

class (E a, E2 a) => F a where
  funF :: a -> a
