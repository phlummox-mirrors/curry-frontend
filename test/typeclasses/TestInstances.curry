
class Eq a where
  (===) :: a -> a -> Bool

class Eq' a where

data T a = T a

data R = R

instance Eq' a => Eq (T a) where
  (===) a b = error ""

-- instance Eq' Prelude.Int where
instance Eq' Int where

test = T (1::Int) === T 2

test2 x y = T x === T y

-- test3 = R === R
