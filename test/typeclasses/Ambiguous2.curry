
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

class I a where
  fun8 :: a -> a

testC1 x = fun x && testC2 x

testC2 x = fun3 x x && testC3 x (error "")

testC3 x y = {-fun5 True && -}testC1 x && fun6 y

