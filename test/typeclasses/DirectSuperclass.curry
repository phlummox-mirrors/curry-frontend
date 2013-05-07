

-- error: 
class A a => A a where
  fun3 :: a -> a

{-
-- todo:
class DirectSuperclass.A a => A a where
  fun3 :: a -> a
-}

class B a where

class B a => C a where

{-
data T a = T a
  
instance A a => A (T a) where
  fun3 x = x
-}
  