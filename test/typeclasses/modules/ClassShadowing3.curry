
module ClassShadowing3 where

import ClassShadowing1

class C a where
  funC :: a -> a -> a

instance C Bool where
