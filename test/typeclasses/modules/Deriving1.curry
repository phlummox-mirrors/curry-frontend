
import Prelude ()
import TCPrelude

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

data X a b = a :=: b | X1 a b
  deriving Eq

