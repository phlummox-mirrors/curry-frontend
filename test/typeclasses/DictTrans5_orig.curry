

class A a where
  funA1 :: a -> a -> Bool
  funA2 :: a -> b -> c
  funA3 :: a -> b -> c
  funA4 :: a -> d -> b -> a

instance A Bool where
  
test x = funA1 x x

test2 = funA1 True False
