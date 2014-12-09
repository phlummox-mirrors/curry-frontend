
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


test1 x | fun x = True


test2 x | fun x = True
        | fun3 x x = False

test3 x y | fun x = True
          | fun3 y y = False