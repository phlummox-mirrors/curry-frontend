

module Dependencies3 (E(..), L(..)) where

class C a where
  funC :: a -> a

class D a where
  funD :: a -> a

data T a = T a

instance C Bool where
  funC x = x

instance D a => C (T a) where
  funC x = x

class E a where

class F a where

class G a where

class G a => H a where

instance G Bool where
instance H Bool where

class K a where

class K a => L a where
