
module DerivingClassesSupported3 where

import Prelude ()
import TCPrelude

data T a = T a
  deriving (Eq, Ord)

