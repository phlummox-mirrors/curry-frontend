
module InstancesHierarchy2b where

import InstancesHierarchy1b

instance (A a, B b) => A (a, b) where
  funA (x, y) = (x, y)
  

  

  