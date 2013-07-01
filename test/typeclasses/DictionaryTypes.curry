

class A a where
  funA :: a -> a

class B a where

class A a => C a where


class (A a, B a) => D a where
  funD :: a -> a


class D a => E a where
  funE1 :: a -> a
  funE2 :: a -> Bool


class F f where
  funF :: f -> Bool -> f

class F g => G g where
  funG :: g -> Bool
