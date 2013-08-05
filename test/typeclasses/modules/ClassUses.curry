
-- module ClassUses where
module ClassUses (C(..), D(..), Def(..), F(..), H(..)) where

class C a where
  funC1 :: a -> a
  funC2 :: a -> a -> Bool
  
class C a => D a where
  funD1 :: a -> Bool
  
class Def a where
  funDef :: a -> a
  funDef x = x

class F a where
  funF :: a -> a
  
instance F Bool where
  funF x = x
  
class H a where
  funH :: a -> a
  
instance (H a, H b) => H (a, b) where
  funH (x, y) = (x, y)
  
