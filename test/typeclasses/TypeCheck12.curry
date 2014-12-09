

class A a where
  funA :: a -> a

class B a where
  funB :: a -> a
  
test x = testA1 x
  where
    testA1 x = testA2 (funA x)
    testA2 x = testA1 (funB x)
    