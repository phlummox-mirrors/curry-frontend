

class A a where
  funA :: a -> a

test x = test2
  where test2 = funA x

