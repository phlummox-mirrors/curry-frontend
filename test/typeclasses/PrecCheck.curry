

fun = 1 * 2 + 2 * 4 + 3 + 4

class Test a where
  funT :: a -> Int
  funT x = 1 * 2 + 2 * 4 + 3 + 4

instance Test Int where
  funT x = 1 * 2 + 2 * 4 + 3 + 4

