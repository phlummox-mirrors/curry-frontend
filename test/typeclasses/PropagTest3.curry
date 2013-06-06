
class A a where
  funA :: a -> a

test4 x = x
  where
  test4' y = funA y
