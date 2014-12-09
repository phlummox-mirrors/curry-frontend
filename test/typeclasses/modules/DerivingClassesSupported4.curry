
module DerivingClassesSupported4 where

import Prelude as TCP

data T a = T a
  deriving (TCP.Eq, TCP.Ord)

