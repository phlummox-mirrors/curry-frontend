

class A a where
  funA1 :: a
  funA2 :: a -> a

instance A Bool where
  funA1 = True
  funA1 = False
  funA2 x = x

tySig :: A a => a
tySig = funA1



instance A a => A [a] where
  funA1 = [funA1, funA1]
  funA1 = [funA1]
  funA2 [x] = [x]
