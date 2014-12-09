
module ClassUsesUse where

-- import ClassUses
import ClassUses (C(..), D(..), Def(..), F(..), H(..))

class D a => E a where
  funE :: a -> a
  
instance C Bool where
  funC1 x = x
  funC2 x y = x == y
  
instance D Bool where
  funD1 = const True
  
test1 x = funC1 True

test2 x = funE x

test3 :: C a => a -> a
test3 x = x

test4 :: E a => a -> a
test4 x = funC1 x

instance (C x, C y) => C (x, y) where
  funC1 x = x
  
-- test5 :: (C a, C b) => 
test5 x y = funC1 (x, y)

-- defaults!

instance Def Bool where
  
  
instance Def Int where
  funDef x = x
  
class F a => G a where
  funG :: a -> a
  
instance G Bool where
  funG x = x

test6 x y = funH (x, y)

  