module List (first) where

first :: [a] -> a
first [] = error "empty"
first (x:_) = x
