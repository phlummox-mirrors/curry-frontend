
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

test = fun 1

test2 = fun True

testA :: C a => a -> a -> Bool
testA = error ""