module List2 (last) where

last :: [a] -> a
last [x] = x
last (_:x:xs) = last (x:xs)
