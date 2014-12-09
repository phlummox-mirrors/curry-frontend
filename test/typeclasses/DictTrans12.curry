
class A a where
  funA :: a -> a

test5 x = y
  where y = funA x


test9 x = y
  where Just (y, [z]) = Just (funA z, [funA y])

test10 x = z
  where Just (y, [z]) = Just (funA z, [funA y])

