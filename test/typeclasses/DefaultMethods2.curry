

class Arb a where
  arb :: a
  arb = error "arb"
  arb2 :: a


instance Arb Bool where
  -- no implementation for arb
  arb2 = True
  arb2 = False


  
arbL :: Arb a => [a]
arbL = [arb, arb]


arbLB = arbL :: [Bool]

class Arb a => Arb2 a where
  arb3 :: a
  arb3 = error "arb3"
  arb4 :: a

instance Arb2 Bool where
  -- no implementation for arb3
  arb4 = True
  arb4 = False



