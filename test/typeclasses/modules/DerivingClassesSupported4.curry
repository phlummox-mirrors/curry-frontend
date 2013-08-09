
module DerivingClassesSupported4 where

import Prelude ()
import TCPrelude as TCP

data T a = T a
  deriving (TCP.Eq, TCP.Ord)

