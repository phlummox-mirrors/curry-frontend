
module Instances where

class C1 a where
  fun1 :: a -> a -> Bool
  fun2 :: a -> a -> Bool

class C2 a
  
data T1 a = T1 a
  
instance C2 a => C1 (T1 a) where
  fun1 x y = True
  fun1 x y = False
  fun2 x y = True
