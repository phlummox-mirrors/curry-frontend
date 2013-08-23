

import Prelude ()
import TCPrelude

data T a b c = T1 | T2 a | T3 a b | T4 a b c | T5 c | T6 a c | a :=: b
  deriving Show

