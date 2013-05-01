
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a


testLC1 x y z = [fun x | fun3 y y,
                         _ <- fun5 z]

testLC1b x y z = [True | fun3 y y,
                         _ <- fun5 z]

testLC2 x y z = [fun x | fun3 y y,
                         fun (fun5 z)]

testLC3 x y z v w = [fun x | let a = fun3 y y
                                 b = fun5 z
                           , fun5 v
                           , _ <- fun5 w]

testLC3b x y z v w = [fun x | fun5 v
                            , _ <- fun5 w]

testLC3c x y z v w = [fun x | let a = fun3 y y
                            , fun5 v
                            , _ <- fun5 w]

testLC3d x y z v w = [fun x | let b = fun5 z
                            , fun5 v
                            , _ <- fun5 w]

testLC4 x y z = [fun x && a && fun b | let a = fun3 y y
                                           b = fun5 z]

testLC5 x y z v = [fun x | let a = fun4 y
                         , fun3 z z
                         , _ <- fun5 v]

testLC6 y = [True | let b = fun5 y]
testLC6b y = [True | let a = fun3 y y]








testDo1 x y z v = do
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

toBool _ = True
  
testDo12b x y z = do
  let a = fun3 y y
      b = fun5 z
  return (fun x && a && toBool b)

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


testDo15 x y z = do
  let ad = fun3 y y
      bd = fun5 z
      cd v = fun2 v
  return (fun x && ad && fun bd)