

class A a where
  funA1 :: a -> a -> Bool
  funA2 :: a -> a

{-
class B a where
  funB1 :: a -> a
  funB2 :: a -> a -> a
  funB3 :: a -> a -> a
  -}

class B a where
  funB1 :: a -> b -> a
  funB2 :: a -> a -> c -> a
  funB3 :: b -> a -> a
  funB4 :: a -> c -> c

class A a => C a where
  funC :: a -> a


class (A a, B a) => D a where
  funD1 :: a -> a
  funD2 :: a -> Bool
  

class E a where


class F a where
  funF :: a -> a

class F a => G a where
  
instance A Int where
  funA1 0 1 = True
  funA1 _ _ = False
  funA2 x = x

instance B Int where
  funB1 x _ = x
  funB2 x _ _ = x
  funB3 _ x = x
  funB4 x y = y
