
{-# LANGUAGE NoMonomorphismRestriction #-}

class A a where
  funA :: a -> a

test :: a -> a
test = (id :: Eq a => a -> a)

-- test' :: Eq a => a -> a
test' = (id :: Eq a => a -> a)

test2 :: a -> a
test2 = (funA :: a -> a)

test3 :: A a => a -> a
test3 = (funA :: A a => a -> a)
