

class C a where
  fun1 :: a -> a
  fun2 :: a -> b -> c

instance C Int where
  fun1 = 1
  fun2 = error ""
  -- error
  -- funx = error ""

instance C Int where
  -- error
  -- fun3 = 2
  fun1 = 1
