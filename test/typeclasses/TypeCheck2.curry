
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

  
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

testDo9 x y z = do
  let a = fun x
      b = fun3 y y
  return True

testDo10 x y z = do
  let a = fun x
      b = fun3 y y
  return (fun4 z)

testDo11 x y z = do
  let a = fun3 y y
      b = fun5 z
  return (fun x)

testDo12 x y z = do
  let a = fun3 y y
      b = fun5 z
  return (fun x && a && fun b)

testDo13 x y z = do
  let a = fun3 y y
  _ <- return (fun4 y)
  _ <- return (fun4 z)
  return (fun x)

testDo14 x y z = do
  let a = fun3 y y
      b = fun y
  _ <- return (fun4 z)
  return (fun x)

testExplTyped x = (fun x :: Bool)

testExplTyped2 x y = (fun x :: Bool) && (fun3 y y :: Bool)

testExplTyped3 x = x :: Bool

testExplTyped4 x = x :: Bool


testMinus = - (fun2 1)
testMinus2 = - (fun2 1 + fun4 1)
testMinus3 = - (fun2 1) + (-(fun4 1))

testEnum = [fun2 1 ..]
testEnum2 = [fun2 1 .. fun4 4]
testEnum3 = [(fun2 1), (fun4 2) ..]
testEnum4 = [(fun2 1), (fun2 2) .. (fun4 3)]


{-
type Rec a = { a :: a, b :: Bool }

testRecConstr x = { a := fun2 x, b := fun x }

testRecConstr2 x = { a := error "", b := fun x }
testRecConstr3 x = { a := fun2 x, b := error "" }
testRecConstr3b x = { a := fun4 x, b := error "" }

testRecConstr4 x = { a := fun4 x, b := fun x }
-}
{-
-- there are some strange compile errors with the following, so
-- I disable this:
testRecSel = { a := 'c', b := True } :> a
testRecSel2 = { a := 'c', b := True } :> b

testRecSel3 x y = { a := fun x, b := fun3 y y } :> a
-}
