f :: Int -> Int
f x = x + 1

g y = h y * k y
  where
    h :: Int -> Int
    h a = a * 2
    k b = b `div` 2
