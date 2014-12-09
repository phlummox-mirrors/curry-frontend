

class A a where
  funA1 :: a -> a -> Bool
  funA2 :: a -> a

{-
class B a where
  funB1 :: a -> a -> a
  funB2 :: a -> a -> a -> a
  funB3 :: a -> a -> a
  funB4 :: a -> a -> a
  -}

class B a where
  funB1 :: a -> b -> a
  funB2 :: a -> a -> c -> a
  funB3 :: A b => b -> a -> a
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

instance A a => A [a] where
  funA1 _ _ = True
  funA2 x = x

instance B a => B [a] where
  funB1 x _ = x
  funB2 x _ _ = x
  funB3 _ x = x
  funB4 x y = y

instance (A a, B a) => F [a] where
  funF x = x

data T a b = T a b

instance (A a, B b) => F (T a b) where
  funF x = x
  
instance A (T a b) where
  funA1 x y = True
  funA2 x = x

instance B (T a b) where
  funB1 = error ""
  funB2 = error ""
  funB3 = error ""
  funB4 = error ""
  
instance C (T a b) where
  funC x = x

instance D (T a b) where
  funD1 x = x
  funD2 x = True

instance G (T a b) where

data S a b = S a b

-- missing functions!
instance B (S a b) where

data U a b = U a b
  
instance B (U a b) where
  funB1 x _ = x
  funB3 _ x = x
  