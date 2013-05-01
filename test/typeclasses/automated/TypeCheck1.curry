
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool
  fun3b :: a -> b -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

class G a where
  fun6 :: a -> Bool
  
test1 = fun 1

test2 = fun True

test3 = fun 'a'

test4 x = fun x


test5 = test4

test6 y = test4 y

test7 x y = test4 x

test8 x y = test4 x && fun3 y y


test9 = test8

test10 x = fun2 x

test11 x = fun2 (fun2 (fun2 x))

test12 x = fun (fun4 x)

test13 x y = fun3 x y

test14 x y = fun3 (fun x) y

test15 x y = fun3 (fun2 x) (fun4 y)

test16 x y = fun3b (fun2 x) (fun4 y)

test17 x y = fun3b (fun2 x) y




testTuple1 x y = (fun x, fun4 y)

testTuple2 x y = (fun x, y)

testTuple3 x y = (fun x, fun2 y)

testList1 x y = [fun x, fun3 y y, fun3 x x]

testList2 x y = [True, False]

testList3 x = [True, False, fun x]

testITE1 x = if fun x then 1 else 2

testITE2 x = if fun x then fun x else fun3 x x

testITE3 x = if True then fun2 'a' else 'b'

testITE4 x = if True then fun2 x else x

testITE5 x y = if fun4 y then fun2 x else x

testITE6 x y = if fun6 y then fun2 x else x


testAppl :: (C a, D b) => b -> a -> Bool
testAppl = error ""

testAppl1 = testAppl

testAppl2 = testAppl 4 'c'

testAppl3 x = testAppl 4 x

testAppl4 x y = testAppl x y

testAppl5 x y = testAppl [x] [[y]]


testOp1 x = fun x && fun3 x x

testOp2 x y = fun x && fun3 y y

testOp3 x y = fun x && fun3 x y

testOp4 x y z = fun x && fun y && fun z


testLambda1 x = (\y -> fun y) x

testLambda2 x = (\y -> fun y) 'a'

testLambda3 x = (\y -> fun y && fun6 y) x

testLambda4 = (\y -> fun y)




testMultiple x = fun2 x
testMultiple x = fun4 x
testMultiple x = fun5 x


testCase1 x =
  case x of
    True -> fun x
    False -> fun4 x

testCase2 x y z =
  case x of
    1 -> fun2 y
    2 -> fun4 z

testCase3 x =
  case fun x of
    True -> False
    False -> True

testCase4 x y =
  case fun x of
    True -> fun3 y y
    False -> True

testCase5 x =
  case x of
    True -> False
    False -> True

testCase6 x =
  case x of
    True -> fun 'c'

testCase7 x y =
  case x of
    True -> fun 'c'
    False -> fun4 y

testCase8 x y =
  case fun x of
    True -> fun4 'c'
    False -> 'd'
