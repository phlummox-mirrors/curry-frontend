
module DerivingClassesSupported2Err where

-- import Prelude

class Eq a where

data T a = T a
  deriving (Eq)

