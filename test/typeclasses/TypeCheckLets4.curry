
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

class G a where
  fun6 :: a -> Bool

class H a where
  fun7 :: a -> a -> Bool

class I a where
  fun8 :: a -> a


testA1 x = fun5 x && testA2 x

testA2 x =
  let Just x = Just $ fun2 y
      Just y = Just $ fun4 x
  in fun3 x x && testA1 x

testA1' x = testA2' x

testA2' x =
  let Just x = Just $ fun8 y
      Just y = Just $ fun4 x
  in testA1' x

testA1'' x = testA2'' x

testA2'' x =
  let x = fun8 y
      y = fun4 x
  in testA1'' x



testI1 x = testI2 x

testI2 z =
  let x = fun8 y
      y = fun4 x
  in testI1 x



testJ1 x = testJ2 x

testJ2 z = fun2 (testJ1 z)



testG1 x = fun x && testG2 x

testG2 z =
  let Just x = Just $ fun2 y
      Just y = Just $ fun4 x
  in fun3 z z && testG1 z

testE1 x = fun x && testE2 x

testE2 z =
  let x = fun2 y
      y = fun4 x
  in fun3 z z && testE1 z



testF1 x = fun x && testF2 x

testF2 x =
  let x = fun2 y
      y = fun4 x
  in fun3 x x && testF1 x



testB1 x =
  let Just y = Just $ fun2 x
  in y

testB3 x =
  let y = fun2 x
  in y

testB2 x =
  let Just y = Just $ fun2 x
  in 'c'


testC1 x =
  let (y, z) = (fun2 x, fun3 x x)
  in x

testC2 x =
  let (y, z) = (fun2 x, fun3 x x)
  in y

testC3 x =
  let (y, z) = (fun2 x, fun3 x x)
  in z

testC4 x =
  let (y, z) = (fun2 x, fun3 x x)
  in (y, z)

testD1 x =
  let ('c', 1, y, z) = ('c', 1, fun2 x, fun3 x x)
  in x



testH z =
  let Just x = Just $ fun2 y
      Just y = Just $ fun4 x
  in (x, y)

