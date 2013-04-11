
module Qualifier where

data TA = TA

fun :: a -> TA -> TA
fun x TA = TA

class Eqb a => Eqa a where
  fun1 :: a -> TA -> TA
  fun1 x TA = TA

instance Eqb a => Eqa (TA a) where
  fun1 x TA = TA


