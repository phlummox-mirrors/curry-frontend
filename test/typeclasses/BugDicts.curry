

class A a where
  funA :: a -> a

class A a => B a where
  funB :: a -> a
  (===) :: a -> a -> a

class B a => C a where
  funC :: a -> a
  (=^=) :: a -> a -> a

instance (A a, A b) => A (a, b) where
  
-- comment/uncomment type sig makes a difference!
test1 :: (C a, B a) => a -> a
test1 x = test2 x

test2 :: (C a, B a) => a -> a
test2 x = test1 x


test3 x = test1 x


-- ----------------------

-- test4 :: a -> a
test4 x = funB (test5 x)

-- test5 :: a -> a
test5 x = funC (test4 x)

test6 x = test4 x


-- ----------------------

test7 x y = funA (x, y)

test8 x y = test7 x y

-- ----------------------


test9 x = x === (test10 x)

test10 x = x =^= (test9 x)

