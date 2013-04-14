

class C a where
  fun :: a -> b -> Bool

instance C (S b) where
  fun = error ""
