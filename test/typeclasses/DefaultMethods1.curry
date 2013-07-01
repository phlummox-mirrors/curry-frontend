

class Eq a where
  (===) :: a -> a -> Bool
  (/==) :: a -> a -> Bool

  (/==) x y = not $ (===) x y
  -- x === y = not $ (/==) x y


instance Eq Bool where
  (===) True True = True
  (===) False False = True
  (===) False True = False
  (===) True False = False

