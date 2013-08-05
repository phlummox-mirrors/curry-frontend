
module HiddenClassMethodsBug1 (D(..)) where

class C a where
  funC :: a -> a

class C a => D a where
  funD :: a -> a