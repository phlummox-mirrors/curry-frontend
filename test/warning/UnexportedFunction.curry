module M (f) where

f :: a -> a
f x = x
  where
    q :: Int -> Int
    q i = i+42

g :: a -> a
g x = x

