
import Prelude hiding (show)

class Show a where
  show :: a -> String

class Read a where
  read :: String -> a


-- ambiguous!
-- testI5 = let x = read "..." in show x

testI6 = let x = read "..." in show (x :: Bool)

testI7 = let x = read "..." in (show :: Bool -> String)

testI8 = read "..."

testI9 = (read "..." :: Bool)

testI10 :: Bool
testI10 = read "..."

testI11 :: a
testI11 = read "..."
 

testI12 :: Show a => a -> String
testI12 a = show a

testI13 :: a -> String
testI13 a = show a

testI14 :: Bool -> String
testI14 a = show a

