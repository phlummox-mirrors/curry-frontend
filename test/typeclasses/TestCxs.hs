

class A a where
  funA :: a -> a

test :: a -> a
test = (id :: Eq a => a -> a)

test2 :: a -> a
test2 = (funA :: a -> a)
