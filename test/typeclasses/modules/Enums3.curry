
import Prelude ()
import TCPrelude

test1 = [1 .. 3]

test2 = [False .. True]

test3 x y = [x .. y]

test4 x y = [(x, x) .. (y, y)]

class C a where
  funC :: a -> a

class D a where
  funD :: a -> a
  
instance (C a, C b) => Enum (a, b) where
  
test5 x y = [funC x .. funD y]
  
data T = T1 | T2 | T3 | T4
  deriving Enum

test6 = [T1 .. T3]

test7 = test3 1 3

instance C Int where

test8 = test4 1 3

test9 = ['a' .. 'e']
