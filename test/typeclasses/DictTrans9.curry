

class A a where
  funA :: a -> a

instance A Char where
instance A Int where
  
toBool _ = True
  
test x = toBool y && toBool z
  where Just (y, [z]) = Just (funA x, [funA x])

test2 x = toBool y && toBool z
  where Just (y, [z]) = Just (funA 'c', [funA (1::Int)])

{-
test3 x = 1
  where Just (y, [z]) = Just (funA x, [funA x])
  -}

test4 x = toBool y
  where Just y = Just (funA (y::Int))

test4b :: A a => a -> a
test4b x = y
  where Just y = Just (funA y)

test5 :: A a => a -> a
test5 x = y
  where Just y = Just (funA y)

test6 = y
  where Just y = Just (funA x)
        x = x

test7 = y
  where Just (y, x) = Just (funA x, y)


{-
test8 x = 1
  where Just (y, [z]) = Just (funA z, [funA y])
  -}

test9 _ = x
  where x = funA x

