
class A a where
  funA :: a -> a

class B a where
  funB :: a -> a

class C a where
  funC :: a -> a

test1 x = (id :: A a => a -> a) x

test2 x = (id :: Bool -> Bool) True

test3 x = (funA :: A a => a -> a) x

test4 x = (funA :: (A a, B a, C a) => a -> a) x

test5 x = (test1 :: (A a, B a) => a -> a) x

