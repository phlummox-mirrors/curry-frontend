

class Arb a where
  arb :: a

instance Arb Bool where
  arb = True
  arb = False

-- works
arbLB :: [Bool]
arbLB = [arb, arb]

arbL :: Arb a => [a]
arbL = [arb, arb]

-- doesn't work!
arbLB'' = arbL :: [Bool]
