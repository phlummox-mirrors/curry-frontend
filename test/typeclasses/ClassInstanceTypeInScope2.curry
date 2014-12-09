
module ClassInstanceTypeInScope2 where

import Prelude as P

class A a where

instance A Char where

instance A Int where

instance A P.Float where

data P = P

-- errors:
-- instance A (P a)
-- instance A Xyz where

-- instance A (P.Char a) where

