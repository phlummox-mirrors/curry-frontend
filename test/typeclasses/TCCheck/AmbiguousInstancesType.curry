
module AmbiguousInstancesType where

class C a where
  funC :: a -> a

class C a => D a where
  funD :: a -> a
  
data T a = T a
