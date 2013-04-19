

class Eq a where
  eq :: a -> a -> Bool

-- listEq :: Eq a => [a] -> [a] -> Bool
listEq (x:xs) (y:ys) = eq x y && eq xs ys
listEq [] [] = True
listEq _ _ = False


-- member :: Eq a => a -> [a] -> Bool
member x (y:ys) | x == y    = True
                | otherwise = member x ys
member x []                 = False
