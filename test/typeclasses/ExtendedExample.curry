

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

  x /= y = not (x == y)
  x == y = not (x /= y)


class Eq a => Ord a where
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool

  compare :: a -> a -> Ordering

  max :: a -> a -> a
  min :: a -> a -> a

  min x y = if x < y then x else y
  max x y = if x > y then x else y

  x < y = compare x y Prelude.== LT
  x <= y = compare x y Prelude.== LT || compare x y Prelude.== EQ
  x > y = y < x
  x >= y = y <= x

  compare x y = if x == y then EQ else if x <= y then LT else GT


instance Eq Bool where
  True == True = True
  False == False = True
  True == False = False
  False == True = False

instance Ord Bool where
  False `compare` False = EQ
  True `compare` True = EQ
  False `compare` True = LT
  True `compare` False = GT

instance Eq Int where
  x == y = x Prelude.== y

instance Ord Int where
  x <= y = x Prelude.<= y

instance Eq Char where
  x == y = x Prelude.== y

instance Ord Char where
  x `compare` y = (ord x) `compare` (ord y)

instance Eq a => Eq [a] where
  [] == [] = True
  [] == (_:_) = False
  (_:_) == [] = False
  (x:xs) == (y:ys) = x == y && xs == ys

instance (Eq a, Eq b) => Eq (a, b) where
  (x, y) == (x', y') = x == x' && y == y'

instance (Eq a, Eq b, Eq c) => Eq (a, b, c) where
  (x, y, z) == (x', y', z') = x == x' && y == y' && z == z'

instance (Eq a, Eq b, Eq c, Eq d) => Eq (a, b, c, d) where
  (x, y, z, u) == (x', y', z', u') = x == x' && y == y' && z == z' && u == u'

data Tree a = Node (Tree a) a (Tree a) | Empty

instance Eq a => Eq (Tree a) where
  Empty == Empty = True
  Node _ _ _ == Empty = False
  Empty == Node _ _ _ = False
  Node tl v tr == Node tl' v' tr' = tl == tl' && v == v' && tr == tr'

class Show a where
  show :: a -> String

class Read a where
  read :: String -> a

instance Show Bool where
  show True = "True"
  show False = "False"

instance Show Int where
  show x = Prelude.show x

instance Show Char where
  show c = Prelude.show c

instance Show a => Show [a] where
  show xs = "[" ++ show' xs
    where show' [] = "]"
          show' [x] = show x ++ "]"
          show' (x:y:ys) = show x ++ ", " ++ show' (y:ys)

instance (Show a, Show b) => Show (a, b) where
  show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance (Show a, Show b, Show c) => Show (a, b, c) where
  show (x, y, z) = "(" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ")"

instance (Show a, Show b, Show c, Show d) => Show (a, b, c, d) where
  show (x, y, z, u) = "(" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ", " ++ show u ++ ")"

instance Show a => Show (Tree a) where
  show Empty = "Empty"
  show (Node tl v tr) = "Node (" ++ show tl ++ ") " ++ show v ++ " (" ++ show tr ++ ")"

instance Ord a => Ord [a] where
  [] <= (_:_) = True
  [] <= [] = True
  (_:_) <= [] = False
  (x:xs) <= (y:ys) = if x < y then True else if x == y then xs <= ys else False

instance (Ord a, Ord b) => Ord (a, b) where
  (x, y) `compare` (x', y') = if x == x' then y `compare` y' else x `compare` x'

instance (Ord a, Ord b, Ord c) => Ord (a, b, c) where
  (x, y, z) `compare` (x', y', z') =
    if x == x'
    then (y, z) `compare` (y', z')
    else x `compare` x'

instance (Ord a, Ord b, Ord c, Ord d) => Ord (a, b, c, d) where
  (x, y, z, u) `compare` (x', y', z', u') =
    if x == x'
    then (y, z, u) `compare` (y', z', u')
    else x `compare` x'
  
-- ------------------------------------------------------------------------------------
-- Tests
-- ------------------------------------------------------------------------------------

testShow1 = show [1::Int, 2, 3]
testShow2 = show ['a', 'b']
testShow3 = show (1::Int)
testShow4 = show [True, False, True]
testShow5 = show ([] :: [Int])
testShow6 = show (1::Int, 'a')
testShow7 = show ('a', 0::Int, True, False)
testShow8 = show ('a', Node Empty (True, 0::Int) (Node Empty (False, 1) Empty), [1::Int,2])

testShow9 :: Show a => a -> String
testShow9 x = show x



testOrd1 :: Int -> Int -> Ordering
testOrd1 x y = x `compare` y

testOrd1a = (1::Int) <= 2
testOrd1b = (2::Int) <= 1
testOrd1c = (1::Int) `compare` 2

testOrd2 :: Char -> Char -> Bool
testOrd2 x y = x <= y

testOrd3 :: Bool -> Bool -> Ordering
testOrd3 x y = x `compare` y

testOrd4 :: [Int] -> [Int] -> Ordering
testOrd4 xs ys = xs `compare` ys

testOrd5 :: (Int, Int) -> (Int, Int) -> Ordering
testOrd5 t t2 = t `compare` t2

testOrd6 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) -> Ordering
testOrd6 t t2 = t `compare` t2

testOrd7 :: (Int, Bool, Char, Int) -> (Int, Bool, Char, Int) -> Ordering
testOrd7 t t2 = t `compare` t2

testOrd8 :: Ord a => a -> a -> Bool
testOrd8 x y = x <= y




testEq1 :: Tree Int -> Tree Int -> Bool
testEq1 t1 t2 = t1 == t2

testEq2 = Node (Node Empty (1::Int, 'a', [True]) Empty) (2, 'b', [False, False]) Empty
  == Node (Node Empty (1, 'a', [True]) Empty) (2, 'b', [False, False]) Empty

testEq3 = Node (Node Empty (1::Int, 'a', [True]) Empty) (2, 'b', [False, False]) Empty
  == Node (Node Empty (1, 'a', [True]) Empty) (2, 'b', [True, False]) Empty

testEq4 :: Eq a => a -> a -> Bool
testEq4 x y = x == y

testEq5 x y = x /= y

