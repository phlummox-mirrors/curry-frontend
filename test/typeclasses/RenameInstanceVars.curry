

data S a = S a

data T a b = T a b

class A a

class B a

class C a where
  fun :: a -> b -> c -> Bool

instance B b => C (S b) where
  fun = error ""
  
instance (A b, B b, B c) => C (T b c) where
  fun = error ""

