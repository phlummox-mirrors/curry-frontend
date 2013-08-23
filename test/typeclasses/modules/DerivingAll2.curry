
import Prelude ()
import qualified TCPrelude as P


data T a b = T1 a | T2 b | T3 b
  deriving (P.Eq, P.Ord)


data S a b c = S1 a b c | S2
  deriving (P.Eq, P.Ord)


data U a = U P.Bool a
  deriving (P.Eq, P.Ord)


-- newtype V a = V a
--  deriving (P.Eq, P.Ord)

data W a b = W (T a b) (S a b a) (U P.Bool)
  deriving (P.Eq, P.Ord)

data X a b = a :=: b | X1 a b
  deriving (P.Eq, P.Ord)

data C0 = C0
  deriving (P.Eq, P.Ord)

data C1 a = C1 a
  deriving (P.Eq, P.Ord)

data C2 a b = C2 a b
  deriving (P.Eq, P.Ord)

data C3 a b c = C3 a b c
  deriving (P.Eq, P.Ord)

data C4 a b c d = C4 a b c d
  deriving (P.Eq, P.Ord)

-- error
{-
data X a = X a Int
  deriving P.Eq
  -}

data BT = BT1 | BT2 | BT3 | BT4
  deriving P.Bounded

data BS = BS1
  deriving P.Bounded



data B2S = B2S1 | B2S2 | B2S3 | B2S4
  deriving P.Bounded

data B2U a = B2U a
  deriving P.Bounded

data B2T a b c = B2T a P.Bool b c B2S (B2U a)
  deriving P.Bounded


data ET = ET1 | ET2 | ET3 | ET4
  deriving P.Enum

data ES = ES1
  deriving P.Enum

data TS a b c = TS1 | TS2 a | TS3 a b | TS4 a b c | TS5 c | TS6 a c | a :~: b
  deriving P.Show
