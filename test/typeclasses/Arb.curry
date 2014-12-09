

class Arb a where
  arb :: a

instance Arb Bool where
  arb = True
  arb = False

-- works
arbLB0 :: [Bool]
arbLB0 = [arb, arb]

-- ------------------------

arbL :: Arb a => [a]
arbL = [arb, arb]

-- doesn't work!
arbLB = arbL :: [Bool]

-- ------------------------

test :: Arb a => a
test = arb

arbL2 :: Arb a => [a]
arbL2 = [test, test]

arbLB2 = arbL2 :: [Bool]

