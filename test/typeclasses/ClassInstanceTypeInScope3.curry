
module ClassInstanceTypeInScope3 where

import qualified Prelude as P

class A a where

-- errors:
-- instance A Char where

-- instance A Int where

-- instance A Float where

instance A P.Char where

instance A P.Int where
