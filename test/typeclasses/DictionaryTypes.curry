

class A a where
  funA :: a -> a

class B a where

class A a => C a where


class (A a, B a) => D a where
  funD :: a -> a


class D a => E a where
  funE1 :: a -> a
  funE2 :: a -> Bool


class F f where
  funF :: f -> Bool -> f

class F g => G g where
  funG :: g -> Bool


class B a => H a where
  funH :: a -> a
  funH2 :: a -> a -> Bool

instance B Bool where

instance B [a] where

instance B (T a b) where
  
instance H Bool where
  funH True = False
  funH2 True True = False

instance H b => H [b] where
  funH [x] = [x]
  funH2 [x] [y] = True

data T a b = T a b

instance (H a, F b) => H (T a b) where
  funH x = x
  funH2 x y = True
