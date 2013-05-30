

class Eq a where
  eq :: a -> a -> Bool

instance Eq Bool where
  eq True True = True
  eq False False = True
  eq True False = False
  eq False True = False

instance Eq Int where
  eq n m = n == m

instance Eq a => Eq [a] where
  eq [] [] = True
  eq (x:xs) (y:ys) = eq x y && eq xs ys

member :: Eq a => a -> [a] -> Bool
member _ [] = False
member x (y:ys) = if eq x y then True else member x ys

test1 = member True [False, False, False]

test2 = member 0 [1, 2, 3, 0]

test3 = member [True] [[False], [False, True, False]]

test4 = member [True] [[False], [False, True, False], [True]]

