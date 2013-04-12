module Qualifier where

data TA = TA

data TB a = TB

fun :: Eq a => a -> TA -> TA
fun x TA = TA
fun x a = a
  where y = 0
        z = 1

class Eqb a
        
class Eqb a => Eqa a where
  fun1 :: a -> TA -> TA
  fun2 :: a -> TA -> TA
  fun1 x TA = TA
  fun1 x y = y

instance Eqb (TB a)
  
instance Eqa (TB a) where
  fun1 x TA = TA
  fun1 x y = y
  fun2 TB TA = TA


class Eqb a => Eqc a where
  fun3 x TA = TA
  fun3 :: a -> TA -> TA

class Eqd a where
  fun4 :: a -> TA -> TA
  fun5 :: a -> TA -> TA
  
instance Eqd TA where
  fun4 x TA = TA
  fun4 x y = y
  fun5 x TA = x
  

  