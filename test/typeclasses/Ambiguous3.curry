
class Show a where
  show :: a -> String

class Read a where
  read :: String -> a

-- ambiguous!
testI5 = let x = read "..." in show x

