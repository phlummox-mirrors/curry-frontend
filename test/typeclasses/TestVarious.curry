

class A a where

class B a where

class E a where

class (A a) => C a where

class (A a, B a, E a) => D a where

class (C a, D a ) => F a where
  funF :: a -> a

class (D a) => G a where

class (F a, G a) => H a where

class I a where

class (I a) => J a where

class (J a) => K a where

class M a where

class (K a, M a) => L a where

class N a where

class O a where

data T a = T a

data S a = S a

instance A a => A [a] where

instance B a => B [a] where

instance A a => A (S a) where

data U a = U a

instance B a => A (U a) where

data V a b = V a b

instance (A a, B b) => E (V a b) where

instance E a => E ((->) a b) where


instance (M a, K a) => I ((->) a b) where


instance N a => O (T a) where

instance O a => N (T a) where


instance N a => N (a, b) where

instance N () where

data Q a = Q a

instance N (Q a) where

data R1 = R1
data R2 = R2
data W a = W a

instance N R1 where

instance N a => N (W a) where



class P a where

class P a => R a where

class (P a, R a) => Q a where

data X a = X a

instance A a => B (X a)

-- ------------------------------------------------------------

class Eq a where
  (===) :: a -> a -> Bool

class Eq' a where

instance Eq' a => Eq (T a) where
  (===) a b = error ""

instance Eq' Int where

-- test = T (1::Int) === T 2

-- test2 x y = T x === T y


instance (Eq a, Eq b) => Eq (a, b) where

instance Eq a => Eq [a] where

instance Eq Bool where

class Eq a => Ord a where

-- ------------------------------------------------------------

{-
class A1 a where
  funA1 :: a -> b -> Bool
  funA2 :: a -> a
  funA3 :: a -> b -> c
  funA4 :: a -> c
  funA5 :: a -> b -> b

class A1 a => B1 a where
  funB1 :: a -> b -> c -> d -> a
  


class C1 a where
  funC1 :: a -> a

class (B1 a, C1 a) => D1 a where
  funD1 :: a -> b -> c -> a


class C1 a => E1 a


class F1 a where

class F1 a => G1 a where

class F1 a => H1 a where
  funH1 :: a -> a

class I1 a where
  funI1 :: a -> b

class J1 a where
  funJ1 :: a -> b
  -}

