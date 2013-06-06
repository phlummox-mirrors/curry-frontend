

class A a where
  funA :: a -> a

class B a where
  funB :: a -> a


{-
test2 z = z
  where test1_1 x = funA x
        test1_2 x = funB x
        test1_3 x = funA z
          where test_1_3_1 x = funA x
                test_1_3_2 x = funB x
                test_1_3_3 x = funA z
                -}



test2 z = z
  where test2_1 x = funA z

toBool _ = True


test3 x = 1
  where Just (y, [z]) = Just (funA x, [funA x])


{-
-- internal error
test8 x = 1
  where Just (y, [z]) = Just (funA z, [funA y])

-- ambiguous
test9 x = 1
  where Just (y, [z]) = Just (funA y, [funA z])
  -}

{-
test10 _ = 1
  where x = funA x
  -}

instance A Int where
  
test11 _ = 1
  where x = funA (x :: Int)