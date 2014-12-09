
module DiamondInsts1 where

class C a where
  funC :: a -> a

instance C Bool where
  funC x = x