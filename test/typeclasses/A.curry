
module A ({-A1, A2, -}TA, funA) where

class A1 a where
  funA1 :: a

class A1 a => A2 a where
  funA2 :: a

class A3 a where
  funA3 :: a

data TA = TA

funA :: a -> TA
funA x = TA

funB :: TA
funB = TA

class A4 a where
  funA4 :: a -> TA
