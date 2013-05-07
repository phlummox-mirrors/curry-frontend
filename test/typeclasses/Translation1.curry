

class A a where
  funA :: a -> a -> Bool
  funA2 :: a -> a

class B a where
  funB1 :: a -> a -- a -> b
  funB2 :: a -> a -> a -- a -> a -> c
  funB3 :: a -> a -> a -- b -> a -> a

class A a => C a where
  funC :: a -> a


class (A a, B a) => D a where
  funD :: a -> a

