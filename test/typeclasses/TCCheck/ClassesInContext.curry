

class NotExistent a => A a where

data T a = T a

instance NotExistent a => A (T a) where

test :: NotExistent a => a -> a
test x = x

