

class A a where

class A a => B a where

class C a where

class D a where

test :: A a => a -> a
test x = x

data T a b = T a b

instance (A a, C b) => D (T a b) where
