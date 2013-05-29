

class Eq a where
  (===) :: a -> a -> Bool

instance Eq Bool where
  True === True = True
  False === False = True
  True === False = False
  False === True = False

instance Eq Int where
  n === m = n == m

instance Eq a => Eq [a] where
  [] === [] = True
  (x:xs) === (y:ys) = x === y && xs === ys

-- member :: Eq a => a -> [a] -> Bool
member _ [] = False
member x (y:ys) = if x === y then True else member x ys

