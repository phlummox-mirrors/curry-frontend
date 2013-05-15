

class A a where
  funA :: a -> a

class B a where
  funB :: a -> a

instance A a => B [a] where

instance A a => B (a, b) where

instance A a => B (a, b, c) where

instance A a => B (a -> b) where

test1 :: a -> a
test1 x = (funA x)

test2 :: A a => a -> a
test2 = test3

test3 :: B a => a -> a
test3 = test2

test4 :: [a] -> [a]
test4 xs = funB xs

-- ok
test5 :: A a => [a] -> [a]
test5 xs = funB xs

test6 :: (A x, A y) => x -> y -> x
test6 x y = funB x

-- ok
test7 :: A a => (a, b) -> (a, b)
test7 (x, y) = funB (x, y)

test8 :: (a, b) -> (a, b)
test8 (x, y) = funB (x, y)

-- ok
test9 :: A a => (a, b, c) -> (a, b, c)
test9 (x, y, z) = funB (x, y, z)

test10 :: (a, b, c) -> (a, b, c)
test10 (x, y, z) = funB (x, y, z)

-- ok
test11 :: A a => (a -> b) -> (a -> b)
test11 f = funB f

test12 :: (a -> b) -> (a -> b)
test12 f = funB f


