
test0 = 1
test0b = 1.0

test1 = 1 + 1

test2 = 1.3 + 2.4

test3 = test1 :: Int
test3b = test1 :: Float

test4 x 1 = x
test4b x 1.0 = x

test5 = 1 + 1.3


test6 :: Num a => a -> a
test6 x = x + 1

test7 :: Fractional a => a -> a
test7 x = x + 1.0


test6a = test6 1
test6b = test6 1.2

test7a = test7 1
test7b = test7 1.2

test8 = 1 :: Int

test9 = 5 `div` 2
test10 = 4 `mod` 3

test11 = - 1
test12 = - 1.0
test13 = - (1 + 2)
test14 = - (1.2 + 1)

test15 = - test2
test16 = - (test6 1)

test17 = - (1::Int)
test18 = - (1::Float)

class C a where
  funC :: a -> a

test19 x = - (funC x)

instance C Int where
  funC x = x

test20 = - (funC 1)

test21 = -(funC (1 :: Int))
