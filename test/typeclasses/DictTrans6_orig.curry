

class A a where
  funA :: a -> a

class B a where
  funB :: a -> b -> a

test :: A b => b -> b
test x = funA x

test2 :: B c => c -> d -> c
test2 x y = funB x y

