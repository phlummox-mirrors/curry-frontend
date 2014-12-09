

class A a where
  funA :: a -> a

instance A Int where
instance A Bool where
instance A (Maybe a) where

test1 x = (id :: A a => a -> a) x

test2 x = (id :: Bool -> Bool) True

test2b x = (id :: Bool -> Bool) x

test3 x = (funA :: A a => a -> a) x

test4 x = (funA :: A a => a -> a) x

test5 x = (test1 :: A a => a -> a) x

test6 x = (funA :: Int -> Int) x

test7 x = (funA :: A a => Maybe a -> Maybe a) x

test8 x = (test1 :: Bool -> Bool) x


class B a where
  funB :: a -> b -> a
  
instance B Bool
  
test9 x y = (funB :: B a => a -> Int -> a) x y

test10 x y = (funB :: Bool -> Int -> Bool) x y

test11 x y = (funB :: B a => a -> b -> a) x y

test12 x y = (funB :: B a => a -> Bool -> a) x y

