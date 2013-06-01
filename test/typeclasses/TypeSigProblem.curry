
class A a where
  funA :: a -> a

instance A Int where

instance A Float where

 -- problem with removing type signature!
test :: A a => a -> Float
test x = 0

test2 :: Float
test2 = 0


test3 = test 1
