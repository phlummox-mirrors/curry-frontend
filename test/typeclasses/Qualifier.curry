
module Qualifier where

data TA = TA

data TB a = TB

fun :: {-Eq a => -}a -> TA -> TA
fun x TA = TA
fun x a = a
  where y = 0
        z = 1
       
class Eqb a
        
class {-Eqb a => -}Eqa a where
  fun1 :: a -> TA -> TA
  fun2 :: a -> TA -> TA
  fun1 x TA = TA
  fun1 x y = y
  fun1 x y = fun2 x y
  fun1 x y = fun x y

instance Eqb (TB a)
  
instance Eqa (TB a) where
  fun1 x TA = TA
  fun2 TB TA = TA
  fun1 x y = y

class Eqb a => Eqc a where
  fun3 x TA = TA
  fun3 :: a -> TA -> TA

class Eqd a where
  fun4 :: a -> TA -> TA
  fun5 :: a -> TA -> TA

instance Eqa TA where

instance Eqd TA where
  fun4 x TA = TA
  fun5 x TA = x
  fun4 x y = y
  fun4 x y = fun5 x y
  fun4 x y = fun1 x y
  fun4 x y = fun4 x y

fun6 :: Eqa a => a -> TA -> TA
fun6 = error ""
-- fun6 = fun1
