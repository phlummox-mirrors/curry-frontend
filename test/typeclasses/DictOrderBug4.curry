

class A a where
  funA :: a -> a

class A a => B a where
  funB :: a -> a

instance (A a, B b, A b) => A (a, b) where
  funA (x, y) = (x, y)


test x y = funA (x, y)

