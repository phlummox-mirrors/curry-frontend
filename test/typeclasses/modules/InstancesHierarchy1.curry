
module InstancesHierarchy1 (C(..), D(..), E(..), F(..)) where

class C a where
  funC :: a -> a
  
class C a => D a where
  funD :: a -> a
  
class D a => E a where
  funE :: a -> a
  
class E a => F a where
  funF :: a -> a
  
instance C Bool where
  funC x = x

 