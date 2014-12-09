

class A a where
  funA :: a -> a

class A a => B a where
  funB1 :: a -> a
  funB2 :: a -> String

class C a where


class D a where
  funD :: a -> a -> String

class D a => E a where
  
class F a where
  funF1 :: a -> a
  funF2 :: a -> a

class F a => G a where
  funG1 :: a -> a
  funG2 :: a -> a

instance (A a, A b) => A (a, b) where
  
toBool _ = True

test1 :: (A a, G b, D c) => a -> b -> c -> Bool
test1 x y z = toBool (funA x) && toBool (funF1 y) && toBool (funD z z)

test2 :: (A a, G b, F b, D c) => a -> b -> c -> Bool
test2 x y z = toBool (funA x) && toBool (funF1 y) && toBool (funD z z)

test3 :: (D c, A a, G b, F b, F b) => a -> b -> c -> Bool
test3 x y z = toBool (funA x) && toBool (funF1 y) && toBool (funD z z)


test4, test5 :: (D c, A a, G b, F b, F b) => a -> b -> c -> Bool
test4 x y z = toBool (funA x) && toBool (funF1 y) && toBool (funD z z)
test5 x y z = toBool (funA x) && toBool (funF1 y) && toBool (funD z z)

