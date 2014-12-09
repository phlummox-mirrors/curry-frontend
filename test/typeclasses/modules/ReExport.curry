

module ReExport (T(..), C(..)) where

data T a = T a

class C a where
  funC :: a -> a

