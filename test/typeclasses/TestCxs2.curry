
class Eq a where

class A a where
  funA :: a -> a

data T a = T a

test4 :: T a
test4 = funA

test5 :: a
test5 = (funA :: A a => a -> a)


test6 :: b -> b
test6 = (funA :: A a => a -> a)

test7 :: b -> b
test7 = (funA :: A a => a)

test8 :: b -> b
test8 = (funA :: A a => a -> Bool)

test9 :: b
test9 = \x -> x