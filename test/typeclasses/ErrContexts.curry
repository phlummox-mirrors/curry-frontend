
class B a where

data T a = T a

data S a b = S a b

-- error
instance B b => B (T a) where

-- error
instance B (S a a) where

-- error
class B b => C a where
  
-- error: 
test1 :: (A a) => a -> a
test1 x = x

test2 :: (B a) => a -> a
test2 x = x

-- error: 
test3 :: (A a, B a) => a -> a
test3 x = x

-- error:
test4 :: (B b) => a -> a
test4 x = x
