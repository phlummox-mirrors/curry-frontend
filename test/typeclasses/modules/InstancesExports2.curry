

module InstancesExports2 (T (..)) where

class A a where
  funA :: a -> a

class C a where
  funC :: a -> a

class D a where
  funD :: a -> Bool

class E a where
  funE :: a -> a -> Bool

class E a => F a where
  funF :: a -> a

data T a = T a

instance A (T a) where
  funA x = x

data T2 a = T2 a

instance A (T2 a) where
  funA x = x

instance C a => C (T a) where
  
  
instance (E a, F a) => D (T a) where
  funD x = True

data S a b c = S a b c

instance (C x, D y, E z) => E (S x y z) where
  funE x y = True

instance E Bool where
  funE x y = x && y
