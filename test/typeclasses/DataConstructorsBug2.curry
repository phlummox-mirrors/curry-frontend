

module DataConstructorsBug2 where

import DataConstructorsBug1

class A a where
  funA :: a -> a

class B a where
  funB :: a -> a
  
C :: a -> a
C x = x

D :: (A a, B a) => a -> a
D x = funA (e x)

e x = funB (D x)
