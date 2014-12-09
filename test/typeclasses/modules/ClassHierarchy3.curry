
module ClassHierarchy3 where

import ClassHierarchy2

class D a => E a where
  funE :: a -> a
  