

class F1 a where
  fun1 :: a -> b -> b -> c -> c
  fun2 :: b -> a -> c -> d
  fun3 :: a -> a -> Bool
  fun4 :: a -> [b] -> (b, b) -> (c -> c) -> a
  fun5 :: a -> Bool
  fun6 :: (Eq a, Eq b) => a -> b -> b -> c -> c
  fun7 :: (Eq a, Eq c, Ord b) =>  b -> a -> c -> d
  fun8 :: (Eq a) => a -> a -> Bool
  fun9 :: a -> a1
  fun10 :: a -> b10 -> b1 -> b
  fun11 :: (Eq (a a), Eq (b b)) => a -> b
  fun12 :: a -> b13
  fun13 :: a -> b12
  
  