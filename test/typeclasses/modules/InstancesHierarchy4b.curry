
module InstancesHierarchy4b where

import InstancesHierarchy1b
import InstancesHierarchy3b

test1 = funA True

test2 x y = funA (x, y)

test3 x = funA (True, x)

test4 x y = funC (x, y)

test5 x = funC (True, x)

  

  