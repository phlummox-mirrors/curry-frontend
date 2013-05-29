
class A a where
  funA :: a -> a
 
test :: (A a) => a -> a
test x = {-funA -}x
-- test x = funA x
