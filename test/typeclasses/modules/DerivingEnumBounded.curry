
data T = T1 | T2 | T3
  deriving (Enum, Bounded)

data T' a b c = T' a b c
  deriving Bounded

