
module InstancesHierarchy3b where

import InstancesHierarchy1b
import InstancesHierarchy2b

instance (A a, B b) => B (a, b) where
  funB x = True

instance (A a, B b) => C (a, b) where
  funC x y = True


