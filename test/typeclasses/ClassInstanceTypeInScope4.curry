
module ClassInstanceTypeInScope4 where

import qualified Prelude as P

class A a where

data Char = Char
data Int = Int
data Float = Float

-- *no* errors:
instance A Char where

instance A Int where

instance A Float where

instance A P.Char where

instance A P.Int where
