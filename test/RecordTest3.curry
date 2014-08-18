type R1 = { f1 :: Bool, f2 :: R2 }
type R2 = { f3 :: Int }

type R3 a = { f4 :: String, f5 :: a }

data T = T (R3 Int)

-- f :: R1 -> R1
-- f x = x + 1

-- g :: R3 Int -> R3 Int
-- g x = not x

r2 :: R2
r2 = { f3 := 0 }

r1 :: R1
r1 = { f1 := False, f2 := r2 }

r3 = { f4 := "", f5 := 1 }

e = { f2 := r3 | r1}