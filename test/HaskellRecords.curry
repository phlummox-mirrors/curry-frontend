module HaskellRecords where

data R a = C { l :: Int, x :: a }
         | D { l :: Int }

-- construction
r1 :: R Bool
r1 = C { l = 42, x = True }

r2 :: R a
r2 = C {}

-- pattern matching
fun :: R a -> Bool
fun C { l = 42 } = True

fun2 :: R a -> Bool
fun2 C {} = False

-- update
upd :: R Bool -> R Bool
upd r = r { x = False, l = 0 }

-- selection
getL :: R a -> Int
getL r = l r