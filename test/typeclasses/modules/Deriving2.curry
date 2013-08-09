
import Prelude ()
import TCPrelude


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

data C0 = C0
  deriving (Eq, Ord)

data C1 a = C1 a
  deriving (Eq, Ord)

data C2 a b = C2 a b
  deriving (Eq, Ord)

data C3 a b c = C3 a b c
  deriving (Eq, Ord)

data C4 a b c d = C4 a b c d
  deriving (Eq, Ord)

-- error
{-
data X a = X a Int
  deriving Eq
  -}