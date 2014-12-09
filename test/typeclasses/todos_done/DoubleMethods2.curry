
class C a where
  fun2 :: a -> Int

-- fun2 :: a -> Int
-- fun2 = error ""


test :: Int
test = fun2
  where fun2 = 2

test' :: Int
test' = let fun2 = 2 in fun2
