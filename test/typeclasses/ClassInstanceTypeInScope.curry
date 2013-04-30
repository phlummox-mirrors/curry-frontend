
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

data U a b = U a | U2 b

-- errors:
-- instance A U where
-- instance A (U a) where
-- instance A (U a b c) where

-- correct:
instance A (U a b) where
