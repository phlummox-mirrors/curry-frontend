module Qual where

f :: a -> ()
f x = g (Qual.g x)
  where g y = y

g :: a -> ()
g _ = ()
