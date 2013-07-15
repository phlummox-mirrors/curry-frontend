
module TestClassExports
  ( test
  , test2
  , test3
  , T (..)
  , S (S1)
  , U (U2)
  , C
  , V
  , D (funD1)
  , E (funE2)
  , F (funF1, funF2)
  , G (..)
  , H (..)
  , I (..)
  , Fun
  ) where

test x = 1

test2 x y = 2

data T a b = T a b

data S a b = S1 a b | S2 a b

data U a b = U0 a b | U1 a b | U2 a b

data V a b

class C var where
  funC1 :: var -> var
  funC2 :: var -> Bool

  funC2 x = True


class D a where
  funD1 :: a -> a
  funD2 :: a -> a

class E a where
  funE1 :: a -> a
  funE2 :: a -> a

class F a where
  funF1 :: a -> a
  funF2 :: a -> a

class G a where
  funG1 :: a -> a
  funG2 :: a -> a

class H a where

class I a where
  funI1 :: a -> Bool
  funI2 :: a -> a -> Int
  funI3 :: a -> a -> a




class Fun a where
  funFun :: a -> a

Fun x = x

-- TODO: check later
-- data Fun2 a = Fun2 a

-- Fun2 x = x


test3 :: C a => a -> a
test3 x = x
