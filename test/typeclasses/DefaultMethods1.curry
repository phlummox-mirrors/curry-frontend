

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

instance Eq a => Eq [a] where
  (===) (x:xs) (y:ys) = (===) x y && (===) xs ys
  (===) [] [] = True
  (===) (_:_) [] = False
  (===) [] (_:_) = False


