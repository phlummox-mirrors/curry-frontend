

data T a b = T a b

class A a where
  funA :: a -> T a a

class B a where
  funB :: a -> T a b

class C a where
  funC :: a -> b -> T a b

class C2 a where
  funC2 :: a -> a -> T a a
  
class D a where
  funD :: a -> a

class E a where
  funE :: a -> a
  
test1 x = funA x

test2 x = funB x

test3 x y = funC x y

test4 x = funC x x

test5 x y = T (funD x) (funE y)

test6 x y = funC x y

test7 x y = funC2 x y