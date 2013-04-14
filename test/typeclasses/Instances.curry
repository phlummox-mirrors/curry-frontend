

class C1 a where
  fun1 :: a -> a -> Bool
  fun2 :: Eq b => a -> a -> b -> Bool
  fun3 :: a -> a -> Bool

class C2 a
  
data T1 a = T1 a
  
instance C2 a => C1 (T1 a) where
  fun1 x y = True
  fun2 x y z = True
  fun1 x y = False

