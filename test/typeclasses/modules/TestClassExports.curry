
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
  , test4
  -- not A!
  , B (B1)
  , test5
  , AClass (..)
  , BClass (..)
  , J (..)
  , K (..)
  , K2 (..)
  , L (..)
  , hiding
  , test6
  , test7
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


data A a b = A1 a b | A2 a b

test4 :: a -> A a a
test4 x = A1 x x

data B a b = B1 a b | B2 a b

test5 :: a -> B a a
test5 x = B1 x x

class AClass a where
  funAC :: a -> A a a

class BClass a where
  funBC :: a -> B a a
  funBC2 :: a -> Int
  


class J a where
  funJ :: a -> Maybe a
  -- check later 
  -- funJ2 :: a -> OtherModule.T a

class K a where
  funK :: a -> a

class K2 a where
  funK2 :: a -> Bool
  
class (K a, K2 a) => L a where
  funL :: a -> a

hiding :: C a => a -> a
hiding x = x

test6 :: (C a, D a, E a) => a -> a
test6 x = x


test7 :: (K a, K2 a, L a) => a -> a
test7 x = x

