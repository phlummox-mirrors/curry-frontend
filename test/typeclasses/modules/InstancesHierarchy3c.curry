
module InstancesHierarchy3c where

import InstancesHierarchy1c as S
import InstancesHierarchy2c as Q

instance (S.A a, S.B b) => S.B (a, b) where
  funB x = True

instance (S.A a, S.B b) => S.C (a, b) where
  funC x y = True


