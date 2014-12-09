
class A a where
  funA :: a -> a -> Bool
  funA2 :: a -> a

class A a => B a where
  funB :: a -> a -> Bool
  funB2 :: a -> a

class B a => C a where
  funC :: a -> a -> Bool
  funC2 :: a -> a

instance A Bool where
  funA True True = True
  funA False True = True
  funA True False = True
  funA False False = False

instance B Bool where
  -- funB not defined!

instance C Bool where
  funC True True = False
  funC True False = True
  funC False False = False
  funC False True = True
  
test1 :: C a => a -> Bool
test1 x = funA x x

test1b = test1 True


test2 :: C a => a -> Bool
test2 x = funB x x

test2b = test2 True

test3 :: C a => a -> Bool
test3 x = funC x x

test3b = test3 True

