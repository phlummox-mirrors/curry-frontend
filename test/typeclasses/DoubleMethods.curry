

-- error 1

class A a where
  -- error: 
  -- fun1 :: a
  fun3 :: a

class B a where
  fun1 :: a


-- error 2

class C a where
  fun2 :: a

fun2 :: a -> Int
fun2 = error ""
