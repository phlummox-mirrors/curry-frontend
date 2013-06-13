

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

class H a where
  funH :: a -> b -> c -> a

test1 :: (A a, C a) => a -> a
test1 x = x

test2 :: (B a, D a) => a -> a
test2 x = x

test3 :: (A a, C b, D c) => a -> b -> c -> a
test3 x y z = x

test4 :: (E a, G b) => a -> b -> a
test4 x y = x

test5 :: (E a, G b, D c) => a -> b -> c -> a
test5 x y z = x

{-
test6 :: H a => a -> b -> c -> a
test6 x y z = x

test7 :: H z => z -> b -> c -> z
test7 x y z = x
-}

test8 :: A a => a -> a -> a
test8 x y = funA x

toBool _ = True

test9 :: (A a, G b, D c) => a -> b -> c -> Bool
test9 x y z = toBool (funA x) && toBool (funG2 y) && toBool (funD z z)

test10 :: (A a, D c, G b) => a -> b -> c -> Bool
test10 x y z = toBool (funA x) && toBool (funF1 y) && toBool (funD z z)
