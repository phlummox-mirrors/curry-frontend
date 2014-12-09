
class A a where
  funA :: a -> a

class B a where
  funB :: a -> a

instance B Char where

instance A Char where
  
toBool :: a -> Bool
toBool x = True
  
test1 z = funA z
  where test1_1 x = funA x
        test1_2 x = funB x
        test1_3 x = funA z
          where test_1_3_1 x = funA x
                test_1_3_2 x = funB x
                test_1_3_3 x = funA z


test2 z = toBool (funA z) && toBool (test1_3 'a') && toBool (test1_2 'c')
    && toBool (test1_1 'c') 
  where test1_1 x = funA x
        test1_2 x = funB x
        test1_3 x = funA z
          where test_1_3_1 x = funA x
                test_1_3_2 x = funB x
                test_1_3_3 x = funA z

