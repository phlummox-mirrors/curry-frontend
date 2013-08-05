
module HiddenClassMethodsBug2 where

import HiddenClassMethodsBug1

class C a where
  funC :: a -> a -> Bool

test x = funC x x
