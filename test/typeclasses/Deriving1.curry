

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

  (/=) x y = not $ (==) x y
  (==) x y = not $ (/=) x y

instance Eq Bool where
  True == True = True
  False == False = True
  True == False = False
  False == True = False
  
  
data T a b = T1 a | T2 b | T3 b
  deriving Eq


data S a b c = S1 a b c | S2
  deriving Eq


data U a = U Bool a
  deriving Eq


newtype V a = V a
  deriving Eq

data W a b = W (T a b) (S a b a) (U Bool)
  deriving Eq

