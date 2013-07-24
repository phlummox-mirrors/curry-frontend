
module TCC (C, D, E) where

class C a where
  funC :: a -> a

class C a => D a where
  funD :: a -> a

class E a where
  funE :: a -> a

instance C Bool where

