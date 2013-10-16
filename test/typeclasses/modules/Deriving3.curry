
import qualified Prelude as P

data T a b = T1 a | T2 b | T3 b
  deriving P.Eq


data S a b c = S1 a b c | S2
  deriving P.Eq


data U a = U P.Bool a
  deriving P.Eq


data V a = V a
  deriving P.Eq

data W a b = W (T a b) (S a b a) (U P.Bool)
  deriving P.Eq

data X a b = a :=: b | X1 a b
  deriving P.Eq

data Y a b = Y1 a b | Y2 a | Y3 b
  deriving P.Eq