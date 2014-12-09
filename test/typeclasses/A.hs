
module A (A1, A2, TA, C2, funA, test) where

class A1 a where
  funA1 :: a

class A1 a => A2 a where
  funA2 :: a

class A3 a where
  funA3 :: a

class A4 a where
  funA4 :: a -> TA
  
data TA = TA

funA :: TA
funA = TA

funB :: TA
funB = TA

instance A1 TA where
  funA1 = TA

class C1 a where
  funC1 :: a

class C1 a => C2 a where
  funC2 :: a

test :: (Eq a, Ord a) => a -> Bool
test x = x == x
