

class A a where
  fun :: a -> a

fun :: a -> a
fun = error ""

class B a where
  fun2, fun3 :: a -> Bool

fun3 :: a -> a -> a
fun3 = error ""

test :: Bool
test = True
