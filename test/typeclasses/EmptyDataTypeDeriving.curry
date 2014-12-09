
-- not OK
data T a
  deriving (Eq)

-- OK
data S a
  deriving ()

-- OK
data Q a

-- OK
newtype P a = Q a
  deriving (Eq)