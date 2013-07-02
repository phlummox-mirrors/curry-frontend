

class Eq0 a where
  (===) :: a -> a -> Bool
  (/==) :: a -> a -> Bool

class Eq0 a => Ord0 a where
  (<==) :: a -> a -> Bool
  
instance Eq0 a => Eq0 [a] where
  (===) x y = True
  (/==) x y = True

