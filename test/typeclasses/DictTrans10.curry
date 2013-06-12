

class B a where
  funB :: a -> a

class B a => C a where
  funC :: a -> a

class D a where
  funD :: a -> a

class E a where
  funE :: a -> a
  
test1 z = 1
  where
    test2 x = funB (test3 x)
    test3 x = funC (test2 x)
      where
        test4 = let test5 x = funB (test6 x)
                    test6 x = funC (test5 x)
                in 1


test8 z = 1
  where
    test2 x = funB (test3 x)
    test3 x = funC (test2 x)
    test3b = funD z
      where
        test4 = let test5 x = funB (test6 x)
                    test6 x = funC (test5 x)
                    test8 x = funE z
                in 1
        test7 x = funD z

test9 z = let test1 x = funD z in 1

test10a z = 1
  where test1 x = funD z

test10b z | True = 1
  where test1 x = funD z

test10c z = let test1 x = funD z in 1

test10d z = [1 | let test1 x = funD z]

test10e z = do
  let test1 x = funD z
  return 1
