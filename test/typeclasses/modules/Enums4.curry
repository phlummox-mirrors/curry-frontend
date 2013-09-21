
import Prelude ()
import TCPrelude

test1 = [1, 3 .. 10]

test2 = [False, True .. True]

test3 x y z = [x, y .. z]

test4 x y z = [(x, x), (y, y) .. (z, z)]

class C a where
  funC :: a -> a

class D a where
  funD :: a -> a

class E a where
  funE :: a -> a
  
instance (C a, C b) => Enum (a, b) where
  
test5 x y z = [funC x, funD y .. funE z]
  
data T = T1 | T2 | T3 | T4
  deriving Enum

test6 = [T1, T2 .. T4]

test7 = test3 1 3 8

instance C Int where

test8 = test4 1 3 20

test9 = ['a', 'c' .. 'z']
