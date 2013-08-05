
module DerivingClassesSupported2Err where

-- import Prelude ()
-- import TCPrelude

class Eq a where

data T a = T a
  deriving (Eq)

