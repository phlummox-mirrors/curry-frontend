
test1 = [1 ..]

test2 = [False ..]

test3 x = [x ..]

test4 x = [(x, x) ..]

class C a where
  funC :: a -> a

instance (C a, C b) => Enum (a, b) where
  
test5 x = [funC x ..]
  
data T = T1 | T2 | T3 | T4
  deriving Enum

test6 = [T1 ..]

test7 = test3 1

instance C Int where

test8 = test4 1

test9 = ['a' ..]

