
class A0 a where
  funA0 :: a -> Bool -> Bool
  funA0 x _ = True

class A1 a where
  funA1 :: a -> a -> a
  funA1 x _ = x


class A2 a where
  funA2 :: a -> a -> Bool
  funA2 x _ = True

class A3 a where
  funA3 :: a -> Bool -> a
  funA3 x _ = x

class A4 a where
  funA4 :: Bool -> a -> a
  funA4 _ x = x

class A5 a where
  funA5 :: Int -> a -> a
  funA5 _ x = x 

class A5 a => A6 a where
  funA6 :: a -> Int -> a
  funA6 x _ = x

class A6 a => A7 a where
  funA7 :: a -> Float -> a
  funA7 x _ = x

class A8 a where
  funA8 :: Float -> a -> a
  funA8 _ x = x

data Y a b c = Y a b c

instance (A1 a, A5 a, A3 a) => A5 (Y a b c) where

instance (A1 a, A5 b, A4 c) => A4 (Y a b c) where

instance (A1 c, A5 b, A4 a) => A8 (Y a b c) where

instance (A1 a, A5 a, A3 a, A2 b, A3 b, A6 c) => A3 (Y a b c) where

instance (A5 a, A6 a, A1 b, A3 c) => A2 (Y a b c) where

instance (A1 a, A1 b, A1 c) => A1 (Y a b c) where

data Z a b c = Z a b c

instance (A5 a, A6 a, A7 a, A1 a) => A8 (Z a b c) where

instance (A1 a, A5 a, A6 a, A7 a) => A5 (Z a b c) where

instance (A5 a, A6 a, A1 a, A7 a) => A4 (Z a b c) where

instance (A5 a, A6 a, A7 a, A1 b) => A3 (Z a b c) where

instance (A1 b, A5 a, A6 a, A7 a) => A2 (Z a b c) where

instance (A5 a, A1 b, A7 a, A6 a) => A1 (Z a b c) where

instance (A7 a, A5 a, A1 b, A6 a) => A0 (Z a b c) where


instance A1 Bool where
instance A3 Bool where
instance A4 Bool where
instance A5 Bool where

instance A1 Int where
instance A3 Int where
instance A5 Int where
instance A6 Int where
instance A7 Int where

-- funA5 + Y
test1 x = funA5 0 (Y x True True)

test1b :: (A5 a, A3 a, A1 a) => a -> Y a Bool Bool
test1b x = funA5 0 (Y x True True)

test2 = funA5 1 (Y True True True)

test3 = funA5 2 (Y 0 True True)

-- funA4 + Y
test4 x y z = funA4 True (Y x y z)

test5 x = funA4 True (Y x 0 True)

-- funA8 + Y
test6 x y z = funA8 0.0 (Y x y z)

test7 x = funA8 0.0 (Y x 0 False)

-- funA3 + Y
test8 x y z = funA3 (Y x y z) True

test9 x = funA3 (Y True x 0) True

-- funA2 + Y

test10 x y z = funA2 (Y x y z) (Y x y z)

test11 x = funA2 (Y x 0 True) (Y x 1 False)

-- funA1 + Y

test12 x y z = funA1 (Y x y z) (Y x y z)

test13 x y = funA1 (Y 0 x True) (Y 0 y False)

-- -------------------------

test14 x y z = funA8 0.0 (Z x y z)

test14b x = funA8 0.0 (Z x 0 True)

test15 x y z = funA5 0 (Z x y z)

test15b y = funA5 0 (Z 0 y False)

test16 x y z = funA4 True (Z x y z)

test16b x = funA4 True (Z x 0 True)

test17 x y z = funA3 (Z x y z) True

test17b x = funA3 (Z x True 0) True

test18 x y z = funA2 (Z x y z) (Z x y z)

test18b x = funA2 (Z x 0 True) (Z x (-1) False)

test19 x y z = funA1 (Z x y z) (Z x y z)

test19b x y z = funA1 (Z x True 0) (Z x False 1)

test20 x y z = funA0 (Z x y z) False

test21 x = funA0 (Z x 0 True) False

-- -------------------------

data T a = T a

instance (A5 a, A3 a) => A7 (T a) where

instance A3 a => A6 (T a) where

instance A3 a => A5 (T a) where

test22 x = funA7 (T x) 0.0

test23 = funA7 (T True) 0.0

