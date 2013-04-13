
module Classes where

class C1 a where
  a, b :: a -> a
  c :: a -> Bool
  d, e :: Eq a => a -> a
  f :: Eq a => a -> Bool



class C1 a => C2 a where
  a2, b2 :: a -> a
  c2 :: a -> Bool
  d2, e2 :: Eq a => a -> a
  f2 :: Eq a => a -> Bool

class (C1 a, C3 a) => C2 a 

-- errors:

-- class C a => C2 b
-- class (C a, C2 b, C4 c) => C3 b

class C3 a where
  fun1 :: a -> a
  fun2 :: a -> b -> c -> d
  -- error
  -- fun3 :: b -> Int
  -- fun4 :: Int
  -- fun5 :: b -> c -> d -> Int