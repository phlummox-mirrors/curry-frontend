

class C a where
  fun2 :: a -> a
  fun2 = error ""


class D a where
  fun2 :: a -> a
  fun2 = error ""
  
instance D Int where
  fun2 x = 1

