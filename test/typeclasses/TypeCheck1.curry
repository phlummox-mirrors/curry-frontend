
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a
  
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

testD2 = testC 4 'c'

testD3 x = testC 4 x

testE x = fun x && fun3 x x

testE2 x y = fun x && fun3 y y

testE3 x y = fun x && fun3 x y

testF x = (\y -> fun y) x

testG x = (\y -> fun y) 'a'

testH x = let y = fun 'a' in y

testH2 x = y
  where y = fun 'a'

testH3 x = let y = fun x in y

testH4 x = y
  where y = fun x


testH5 x z = let y = fun x in z

testH6 x z = let y = fun x in y


testH7 x z = let y = fun x && fun3 x x in (x, y)

testH8 x y = let x' = fun x
                 y' = fun y
             in (x', y')

testH9 x y = let x' = fun x
                 y' = fun3 y y
             in (x', y')

testH10 x y = let x' = fun x
                  y' = fun x
              in (x', y')

testH11 x = let x' = let x'' = fun x in x'' in x'

testH12 x = let y = 'a' : x in y

testH13 x = let y = fun 'a' in fun3 x x && y


testI1 = 1
testI2 = 'a'


testTuple x y = (fun x, fun4 y)

testTuple2 x y = (fun x, y)

testTuple x y = (fun x, fun2 y)

testList x y = [fun x, fun3 y y, fun3 x x]

testList2 x y = [True, False]

testList3 x = [True, False, fun x]

testITE x = if fun x then 1 else 2

testITE2 x = if fun x then fun x else fun3 x x

testITE3 x = if True then fun2 'a' else 'b'

testITE4 x = if True then fun2 x else x

testITE5 x y = if fun4 y then fun2 x else x