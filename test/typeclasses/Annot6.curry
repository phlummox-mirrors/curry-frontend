

class A a where
  funA :: a -> a

toBool x = True
  
test x = toBool (test3 x) && toBool (test4 (error ""))
  where -- test2 = funA x
        test3 y = funA y
        test4 y = funA x
        

