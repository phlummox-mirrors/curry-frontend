
{-
class A a where

class C a where

class D a where

data T a b = T a b

instance (A a, C b) => D (T a b) where
-}


class A a where
  -- funA :: a -> a

class C a where
  -- funC :: a -> a

data T a b = T a b

type DictD a = ()

dict :: (A a, C b) => DictD (T a b)

dict = ()

-- ---------------------------------

data S a = S a

type DictD2 a = S a

dict2 :: (A a, C b) => DictD2 (T a b)
dict2 = S (error "")

