

funA :: a -> a
funA x = x

test1 x = (id :: a -> a) x

test2 x = (id :: Bool -> Bool) True

test2b x = (id :: Bool -> Bool) x

test3 x = (funA :: a -> a) x

test4 x = (funA :: a -> a) x

test5 x = (test1 :: a -> a) x

test6 x = (funA :: Int -> Int) x

test7 x = (funA :: Maybe a -> Maybe a) x

test8 x = (test1 :: Bool -> Bool) x



funB :: a -> b -> a
funB x _ = x

test9 x y = (funB :: a -> Int -> a) x y

test10 x y = (funB :: Bool -> Int -> Bool) x y

test11 x y = (funB :: a -> b -> a) x y

test12 x y = (funB :: a -> Bool -> a) x y

