
module ClassInstanceTypeInScope5 where

class A a where

-- all errors:
instance A Int where

instance A Int where

instance A Bool where

instance A Prelude.Bool where
