
class A a where
  funA :: a -> a

class B a where
  funB :: a -> a -> Bool
  
test1 x = funA x

test2 x y = funB x y

test3 x y = funB (funA x) y

x === y = funB (funA x) y




(=&=) :: A a => a -> b -> c -> a
(x =&= y) z = funA x



(f x y) z = funA x

((g x) y) z = funA x

