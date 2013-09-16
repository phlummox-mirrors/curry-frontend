

class C a where
  funC :: a -> a

class D a where

class E a where

class F a where
  funF :: a -> a

instance (D a, E b) => C (a, b) where
  funC x = x

fun1 x = fun2 True
  where
  fun2 z = funC (x, z)
  -- fun3 z = funC (x, z)

test1 = fun1 (1::Int)

instance E Bool where
instance D Int where


{-
toBool :: a -> Bool
toBool _ = True
  
fun1 x y = fun2 True
  where
    fun2 z = toBool (funC (funF x)) && toBool (funC (funF
    -}