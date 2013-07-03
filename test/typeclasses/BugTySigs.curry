

class A a where
  funA :: a -> a

class A a => B a where
  funB :: a -> a
  (===) :: a -> a -> a

class B a => C a where
  funC :: a -> a
  (=^=) :: a -> a -> a

class D a where

-- problem with second type check!
test11 x = (funB :: (D a, C a) => a -> a) x

