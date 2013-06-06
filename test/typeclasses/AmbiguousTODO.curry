

class A a where
  funA :: a -> a

instance A Int where

-- all these throw internal errors!

test10 y = y
  where x = funA x



test8 x = 1
  where Just (y, [z]) = Just (funA z, [funA y])


test11 _ = 1
  where x = funA x
