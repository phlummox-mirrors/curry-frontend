
module TestClassExports2 (J (..), A (..)) where

data A a

data B a 

class J a where
  funJ :: a -> Maybe a
  -- funJ2 :: a -> Int

  funJ3 :: a -> A a
  funJ4 :: a -> B a