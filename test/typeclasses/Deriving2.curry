

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

  (/=) x y = not $ (==) x y
  (==) x y = not $ (/=) x y

  {-
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
  -}
class  (Eq a) => Ord a  where
    compare              :: a -> a -> Ordering
    (<), (<=), (>=), (>) :: a -> a -> Bool
    max, min             :: a -> a -> a

    -- Minimal complete definition:
    --      (<=) or compare
    -- Using compare can be more efficient for complex types.
    compare x y
         | x == y    =  EQ
         | x <= y    =  LT
         | otherwise =  GT

    x <= y           =  compare x y Prelude./= GT
    x <  y           =  compare x y Prelude.== LT
    x >= y           =  compare x y Prelude./= LT
    x >  y           =  compare x y Prelude.== GT

    -- note that (min x y, max x y) = (x,y) or (y,x)
    max x y
         | x <= y    =  y
         | otherwise =  x
    min x y
         | x <= y    =  x
         | otherwise =  y 

instance Eq Bool where
  True == True = True
  False == False = True
  True == False = False
  False == True = False

instance Ord Bool where
  True <= True = True
  False <= True = True
  True <= False = False
  False <= False = True
  
data T a b = T1 a | T2 b | T3 b
  deriving (Eq, Ord)


data S a b c = S1 a b c | S2
  deriving (Eq, Ord)


data U a = U Bool a
  deriving (Eq, Ord)


newtype V a = V a
  deriving (Eq, Ord)

data W a b = W (T a b) (S a b a) (U Bool)
  deriving (Eq, Ord)

data X a b = a :=: b | X1 a b
  deriving (Eq, Ord)
  
-- error
{-
data X a = X a Int
  deriving Eq
  -}