test :: a
test = x
  where
    x :: b
    x = unknown

test1 :: a
test1 = x
  where x :: a
        x free

test2 :: a -> b
test2 = let x = unknown :: a -> b in x

test3 :: a -> b
test3 = let x free in x :: a -> b

test4 :: (Bool, ())
test4 = (x, x)
  where x free

test5 :: (Bool, ())
test5 = (x, x)
  where
    x :: a
    x = unknown