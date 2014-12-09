

class A a where
  funA :: a -> a

class B a where
  funB :: a -> Bool

id x = funA x

x $ y = funA x

x == y = funA x

fst x = funA x

snd x = funB x
