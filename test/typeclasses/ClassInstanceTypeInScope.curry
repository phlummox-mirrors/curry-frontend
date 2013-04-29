
module ClassInstanceTypeInScope where

class A a where

-- error:
-- instance B T where

-- error:
-- instance A P where

data S a = S a

instance A (S a) where
instance A (ClassInstanceTypeInScope.S a) where

newtype T a = T a

instance A (T a) where
instance A (ClassInstanceTypeInScope.T a) where
