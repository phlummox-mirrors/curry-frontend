
module Warnings (test1) where

class A a where
  funA1 :: a -> a
  funA2 :: a -> a

class B a where
  funB :: a -> a
  
instance A Int where
  funA1 x = x

instance A Bool where
  funA1 x = x
  funA2 _ = True

test1 = 1

test2 :: A a => a -> a
test2 x = x

test3 x = 1

test4 y = 2
