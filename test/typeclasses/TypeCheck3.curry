
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

test0 x = fun x

test1 x = fun2 x
test1 x = fun4 x

test2 x = fun x
test2 x = fun3 x x

test3 x = fun2 x
test3 x = fun4 x
test3 x = fun5 x

test4 x = fun2 x
test4 x = fun4 x
test4 x = x

test5 x = fun x
test5 x = fun x && fun x
