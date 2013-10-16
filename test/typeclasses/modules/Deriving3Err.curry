
data S a = S a

data T a = T (S a)
  deriving (Eq)

