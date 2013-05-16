
class A a where
class B a where

test1 :: a -> a
test1 = (id :: A a => a -> a)

fun2 :: a -> b
fun2 = error ""

test2 :: a -> b
test2 = (fun2 :: (A a, B b) => a -> b)

test3 :: a -> b
test3 = (fun2 :: (A c, B d) => c -> d)

test4 :: a -> b
test4 = (fun2 :: (B d) => c -> d)

test5 :: a -> b
test5 = (fun2 :: (B c) => c -> d)

test6 :: a -> b
test6 = (fun2 :: (A c, B c, A d, B d) => c -> d)
