
class A a where
  funA :: a -> a


class A a => B a where

instance (A a, A b) => A (a, b) where
  funA = error ""


test1 :: (A a, A b) => a -> b -> (a, b)
test1 x y = funA (x, y)

test2 :: (B a, B b) => a -> b -> (a, b)
test2 x y = funA (x, y)

test3 :: (A a, B b) => a -> b -> (a, b)
test3 x y = funA (x, y)

test4 :: (B a, A b) => a -> b -> (a, b)
test4 x y = funA (x, y)

test5 x y z u = funA ((x, y), (z, u))
