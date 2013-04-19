
class A a
class B a

data T a b c = T a b c

data S a b c d = S a b c d

instance A (T a b c) where

instance B (T a b c) where

-- errors:
-- instance B (T a b a) where
-- instance B (T a b b) where

-- instance B (S a a a a) where
-- instance B (S a b a b) where
