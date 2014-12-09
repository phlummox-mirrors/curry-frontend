
class A a where
  funA :: a -> a

class B a where
  funB :: a -> a -> a

test = x
  where
  Just x = Just $ funA (f x)
  f y = funB x x
  
  