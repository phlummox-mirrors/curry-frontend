
module InstancesHierarchy1b where

class A a where
  funA :: a -> a
  
class A a => B a where
  funB :: a -> Bool
  
class B a => C a where
  funC :: a -> a -> Bool

instance A Bool where
  funA x = x
  

  