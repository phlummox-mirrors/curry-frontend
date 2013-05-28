
class A a where
  funA :: a -> a

class B a where
  funB :: a -> a -> Bool
  
instance A a => A [a] where
  funA xs = xs

instance B [a] where
  funB x y = True
  
test1 x = funA x

test2 x = funB (funA x) x

test3 x = funA [x]

toBool x = True

test3b x y = toBool (funA x) && toBool (funA y)

test3c x = funA [[x]]

test4 x = funB [x] [x]

test5 x y = funB [x] [x] && funB [y] [y]


