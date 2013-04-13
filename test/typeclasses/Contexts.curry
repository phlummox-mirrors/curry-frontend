

a :: Eq a => a -> a -> Bool
a = error ""

b :: (Eq a, Ord b) => a -> b -> c -> Bool
b = error ""

b2 :: a -> a -> Bool
b2 = error ""

-- error:
c :: Eq a => c -> Bool
c = error ""

-- error:
d :: Eq a => Bool
d = error ""

-- error:
e :: (Eq a, Ord b) => c -> d -> Bool
e = error ""

-- error:
f :: Eq (f a) => a -> a -> Bool
f = error ""

-- error (TODO: Int is not a type variable!):
g :: (Eq (f a), Ord (f Int)) => Bool
g = error ""

class Eq a where
  fun1 :: a -> b -> c
  fun2 :: Eq b => a -> b -> Bool
  -- errors:
  fun3 :: Eq c => a -> Bool
  fun4 :: Eq d => Bool
  fun5 :: Eq d => a -> a -> Bool