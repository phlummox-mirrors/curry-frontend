
import Float

class A a where
  funA :: a -> a

instance A Int where

instance A Float where

test0 = 0

test0b = funA 0

test0c = funA 0.0

test0d = test0b
  
test1 = 0 + (funA 1)

test2 = 0 + 1

test3 = 0.0

test4 = 0.0 +. (funA 1.0)

test5 = 0.0 +. 1.0

test6 = funA 0.0

test7 = funA 0 +. 1.0

test8 = 0 +. 1.0

test9 = funA 0 +. funA 1.0

