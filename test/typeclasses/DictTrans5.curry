

class A a where
  funA1 :: a -> a -> Bool

instance A Bool where
  
test x = funA1 x x

test2 = funA1 True False
