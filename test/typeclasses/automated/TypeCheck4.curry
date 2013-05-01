
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








