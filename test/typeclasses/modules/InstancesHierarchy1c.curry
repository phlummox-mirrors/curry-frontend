
module InstancesHierarchy1c (A(..), B(..), C(..), D(..), T(..)) where

data T a = T a

class A a where
  funA :: a -> a
  
class A a => B a where
  funB :: a -> Bool
  
class B a => C a where
  funC :: a -> a -> Bool

instance A Bool where
  funA x = x
  
class D a where
  funD :: a -> T a
  