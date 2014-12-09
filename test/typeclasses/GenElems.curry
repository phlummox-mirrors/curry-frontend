

class A a where
  funA :: a -> a

class B a where
  funB :: a -> a

class (A a, B a) => C a where
  funC :: a -> a

class C a => D a where


instance A Bool where
  funA False = True
  funA True = False

instance A Int where
  -- missing implementation


instance A a => A [a] where
  funA x = x



test1 = funA (0 :: Int)

test2 = funA True

test3 = funA [True]

