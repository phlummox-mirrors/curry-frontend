
module ListTypeCheckBug
  (

  ) where
  

class Eq a where
  (==) :: a -> a -> Bool

class Eq a => Ord a where
  (<=) :: a -> a -> Bool

insertBy :: (a -> a -> Bool) -> a -> [a] -> [a]
insertBy = error ""
-- insertBy _ x []     = [x]
-- insertBy le x (y:ys) = if le x y
--                          then x : y : ys
--                          else y : insertBy le x ys


--- Sorts the given list
sort :: Ord a => [a] -> [a]
sort = foldr insert []

--- Inserts an element in the list according to the ordering
insert :: Ord a => a -> [a] -> [a]
-- insert x [] = [x]

-- insert x (y:ys) = if x <= y
--                     then (error "") -- x : y : ys
--                     -- BUG BUG BUG BUG BUG BUG BUG
--                     else y : insertBy x ys


insert x (y:ys) = case x <= y of False -> y : insertBy x ys
                    -- then (error "") -- x : y : ys
                    -- BUG BUG BUG BUG BUG BUG BUG
                    -- else y : insertBy x ys

