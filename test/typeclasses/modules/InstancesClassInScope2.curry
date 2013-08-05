
module InstancesClassInScope2 where

import InstancesClassInScope1 as I

class D a where

instance D Bool where

instance InstancesClassInScope2.D Char where

instance C Bool where

instance I.C Bool where

test :: (D a, InstancesClassInScope2.D a, C a, I.C a) => a -> a
test x = x
