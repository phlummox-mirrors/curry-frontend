

class A a where
  funA :: a -> a

test :: A b => b -> b
test x = funA x
