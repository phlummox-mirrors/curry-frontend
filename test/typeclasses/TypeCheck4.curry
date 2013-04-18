
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

testCase x =
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





testDo x y z v = do
  True <- return (fun x)
  'c' <- return (fun4 y)
  return (fun z)
  return (fun v)

testDo2 x = do
  return x

testDo3 = do
  return (fun 'c')

testDo4 = do
  return (fun3 'd' 'c')
  return (fun 'c')

testDo5 = do
  _ <- return (fun3 'd' 'c')
  return (fun 'c')

testDo6 x y z = do
  _ <- return (fun3 x y)
  return (fun z)

testDo7 x y z = do
  return (fun3 x y)
  return (fun z)

testDo8 x y z = do
  _ <- return (fun3 x x)
  return (fun z)



testExplTyped x = (fun x :: Bool)

testExplTyped2 x y = (fun x :: Bool) && (fun3 y y :: Bool)

testExplTyped3 x = x :: Bool

testExplTyped4 x = x :: Bool


testMinus = - (fun2 1)
testMinus2 = - (fun2 1 + fun4 1)
testMinus3 = - (fun2 1) + (-(fun4 1))

