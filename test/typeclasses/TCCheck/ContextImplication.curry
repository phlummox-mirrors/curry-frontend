

class A a where

class A a => B a where

class C a where

data T a = T a 

instance C a => A (T a) where

instance B (T a) where

  