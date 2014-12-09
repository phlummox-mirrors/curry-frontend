

class C a where
  fun :: a -> a -> Bool
  fun = 1

data T a = T a
data S a = S a
data R a = R a
  
instance C (T a) where
  fun = error ""

instance C (S a) where
  fun = error ""

instance C (R a) where
  fun = error ""


test = fun
-- test = fun2
