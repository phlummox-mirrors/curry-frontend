
module InstancesHierarchy2c where

import qualified InstancesHierarchy1c as T

instance (T.A a, T.B b) => T.A (a, b) where
  funA (x, y) = (x, y)
  

  

  