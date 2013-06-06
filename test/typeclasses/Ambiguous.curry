

class A a where
  funA :: a -> a


test9 x = 1
  where Just (y, [z]) = Just (funA y, [funA z])

