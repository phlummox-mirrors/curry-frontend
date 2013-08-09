
module ClassShadowing2 where

import ClassShadowing1

class C a where
  funC :: a -> a -> a

test :: C a => a -> a
test x = x
