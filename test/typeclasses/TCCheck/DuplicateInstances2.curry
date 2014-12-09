
class C a where

class C a => D a where

data T a = T a

class F a where

instance F a => C (T a) where

instance F a => D (T a) where

instance F a => D (T a) where

