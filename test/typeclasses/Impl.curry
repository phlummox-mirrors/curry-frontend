

class A a where
  funA :: a -> a

class B a where
  funB :: a -> a

instance A a => B [a] where
  
test1 :: a -> a
test1 x = (funA x)

test2 :: A a => a -> a
test2 = test3

test3 :: B a => a -> a
test3 = test2

test4 :: [a] -> [a]
test4 xs = funB xs

test5 :: A a => [a] -> [a]
test5 xs = funB xs

test6 :: (A x, A y) => x -> y -> x
test6 x y = funB x

