module HaskellRecords (R (C)) where

data R a = C { l :: Int, x :: a }

-- construction
r1 = C { l = 42, x = True }

r2 = C {}

-- pattern matching
fun C { l = 42 } = True

fun2 C {} = False

-- update
upd r = r { x = False, l = 0 }

-- selection
getL :: R a -> Int
getL r = l r