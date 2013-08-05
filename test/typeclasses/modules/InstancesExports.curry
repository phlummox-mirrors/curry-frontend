

module InstancesExports (T (..)) where

class A a where

class C a where

class D a where

class E a where

class E a => F a where

data T a = T a

instance A (T a) where

data T2 a = T2 a

instance A (T2 a) where

instance C a => C (T a) where


instance (E a, F a) => D (T a) where

data S a b c = S a b c

instance (C x, D y, E z) => E (S x y z) where

instance E Bool where
