

class A a where

class A a => B a where

class B a => C a where

data T a = T a

-- instance A (T a) where

-- instance B (T a) where

instance C (T a) where

