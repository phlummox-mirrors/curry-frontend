
module ClassesAndInstances where

class C1 a where
  a, b :: a -> a
  c :: a -> Bool
  d, e :: Eq a => a -> a
  f :: Eq a => a -> Bool
  h = 1
  i = 2


class C1 a => C2 a where
  a2, b2 :: a -> a
  c2 :: a -> Bool
  d2, e2 :: Eq a => a -> a
  f2 :: Eq a => a -> Bool

class (C1 a, C3 a) => C2 a

-- errors:

-- class C a => C2 b
-- class (C a, C2 b, C4 c) => C3 b

instance C1 (T a) where
  a = 1
  b = 2


instance C1 a => C2 (T a) where
  c = 1
  d = 2
