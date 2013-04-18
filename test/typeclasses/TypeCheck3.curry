
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool


test = fun 1

test2 = fun True

test3 = fun 'a'

test4 = test2

test5 x = fun x



testA :: (C a, D b) => a -> a -> b -> Bool
testA = error ""

testB = testA

testC :: (C a, D b) => b -> a -> Bool
testC = error ""

testD = testC

testE x = fun x && fun3 x x

testE2 x y = fun x && fun3 y y

testE3 x y = fun x && fun3 x y

testF x = (\y -> fun y) x

testG x = (\y -> fun y) 'a'
