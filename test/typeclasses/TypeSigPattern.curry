
class A a where
  funA :: a -> a

test1 = x
  where
    x :: A a => a
    Just x = Just $ error ""


