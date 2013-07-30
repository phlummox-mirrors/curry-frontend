
module InstancesHierarchy4c where

import InstancesHierarchy1c as O
import InstancesHierarchy3c as P

test1 = O.funA True

test2 x y = O.funA (x, y)

test3 x = O.funA (True, x)

test4 x y = O.funC (x, y)

test5 x = O.funC (True, x)

instance O.D Bool where
  funD x = O.T x


