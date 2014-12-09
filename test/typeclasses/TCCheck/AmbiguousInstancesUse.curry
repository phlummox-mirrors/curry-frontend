
import AmbiguousInstancesType

import AmbiguousInstances1
import AmbiguousInstances2

class F a where

instance F a => D (T a) where
  