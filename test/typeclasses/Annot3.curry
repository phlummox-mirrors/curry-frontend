
class A a where
  funA :: a -> a

test1 x = funA x
  
test2 x | True = funA x
        | False = funA x

test3 x = funA x
test3 x = funA x
test3 x = funA x

test4 x = x
  where
  test4' x = funA x
