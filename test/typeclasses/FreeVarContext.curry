

class A a where

test = 1
  where -- x :: Int
        -- x :: a
        -- x :: Int -> Int
        -- x :: A a => Int
        x :: A a => a
        x free
