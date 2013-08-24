

import Prelude ()
import TCPrelude

infixl 3 :==:
infixr 8 :~:

data T a b c = T1 | T2 a | T3 a b | T4 a b c | T5 c | T6 a c
             | a :=: b | a :==: b | a :~: c
  deriving Show

