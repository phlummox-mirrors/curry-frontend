
class B a where

class A a where
  funA :: B a => a -> a -> a

class C a where
  funC :: B b => a -> b -> a
  funC2 :: a -> a



