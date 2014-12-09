

class A a where
  funA :: a -> a -> a

class C a where
  funC :: a -> Bool

class D a where
  funD :: a -> a -> a -> a -> Bool

class E a where
  funE :: a -> a

class F a where
  funF :: a -> a -> Bool

instance A Bool where

instance A Int where

instance C Char where

instance C Int where

instance C Bool where

instance D Float where

instance E Float where


test1 x = funA x x

test2 x = funA True False

test3 x = funA (1::Int) (2::Int)

test5 x = (&&) (funC True) (funC (1::Int))

test6 x = (&&) (funC x) ((&&) (funC True) (funC (1::Int)))



test8 :: (A a, C c, D d, E e) => a -> b -> c -> d -> e -> f
test8 x y z u v = error ""

test9 x = test8 True (1::Int) 'a' x (1.0::Float)


test10 x y = x `funF` y

test11 x y = (x `funF`) y

test12 x y = (`funF` y) x


