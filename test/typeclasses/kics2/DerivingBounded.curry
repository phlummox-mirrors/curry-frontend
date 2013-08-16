
import Prelude ()
import TCPrelude

data S = S1 | S2 | S3 | S4
  deriving (Eq, Bounded)

data U a = U a
  deriving (Eq, Bounded)
  
data T a b c = T a Bool b c S (U a)
  deriving (Eq, Bounded)

