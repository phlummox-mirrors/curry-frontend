

class A a where
  funA :: a -> a


  {-
test10 y = y
  where x = funA x



test8 x = 1
  where Just (y, [z]) = Just (funA z, [funA y])
  -}

test9 x = 1
  where Just (y, [z]) = Just (funA y, [funA z])

{-
test11 _ = 1
  where x = funA x

 -}
