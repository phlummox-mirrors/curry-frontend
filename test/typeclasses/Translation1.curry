

class A a where
  funA :: a -> a -> Bool
  funA2 :: a -> a

  {-
class B a where
  funB1 :: a -> a
  funB2 :: a -> a -> a
  funB3 :: a -> a -> a
  -}

class B a where
  funB1 :: a -> b
  funB2 :: a -> a -> c
  funB3 :: b -> a -> a

class A a => C a where
  funC :: a -> a


class (A a, B a) => D a where
  funD :: a -> a

