



class A a where
  testA :: a -> a
  testA2 :: a -> a


class A a => B a where
  testB :: a -> a

class C a where

instance C Prelude.Bool where

