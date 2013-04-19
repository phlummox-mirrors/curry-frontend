
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a


test1 x y z = [fun x | fun3 y y,
                       _ <- fun5 z]

test2 x y z = [fun x | fun3 y y,
                       fun (fun5 z)]

