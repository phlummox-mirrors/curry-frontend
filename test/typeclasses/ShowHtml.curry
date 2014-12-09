
module ShowHtml where

class C2 a => C1 a where
  a, b :: a -> a
  c :: a -> Bool
  d, e :: Eq a => a -> a
  f :: Eq a => a -> Bool
  f x = 10


instance (C3 a, C4 b) => C5 (T a b) where
  a 5 = 10


fun :: Eq a => a -> b -> Int
fun = fun2

fun2 x y = 1

