

class A3 a where
  funA3 :: a -> Bool -> a
  funA3 x _ = x

class A5 a where
  funA5 :: Int -> a -> a
  funA5 _ x = x

class A5 a => A6 a where
  funA6 :: a -> Int -> a
  funA6 x _ = x

class A6 a => A7 a where
  funA7 :: a -> Float -> a
  funA7 x _ = x


data T a = T a

instance (A5 a, A3 a) => A7 (T a) where

instance A3 a => A6 (T a) where

instance A3 a => A5 (T a) where
