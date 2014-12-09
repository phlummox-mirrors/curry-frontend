
module ClassInstanceTypeInScope where

class A a where

-- error:
-- instance B T where

-- error:
-- instance A P where

data S a = S a

instance A (S a) where

newtype T a = T a

instance A (T a) where

data S2 a = S2 a
instance A (ClassInstanceTypeInScope.S2 a) where

data U a b = U a | U2 b

-- errors:
-- instance A U where
-- instance A (U a) where
-- instance A (U a b c) where

-- correct:
instance A (U a b) where

instance A Char where

instance A Int where

instance A Prelude.Float where



-- errors:
-- instance A (Char a) where
-- instance A (Prelude.Char a) where

instance A (Maybe a) where

-- error:
-- instance A Maybe where


data Either a b = Either a b

-- *no* error: 
instance A (Either a b) where

type F a = S a

-- error:
-- instance A F where

instance A () where

instance A (a, b) where

instance A (a, b, c) where

instance A [a] where

instance A (a -> b) where

