module Diamond (diamond, tab, size) where

import List (last)
import List

import List

seven = (1 + (2 * 3))
seven1 = 1 + 2 * 3

exceptions =
  [ "InvalidStatusCode"
  , "MissingContentHeader"
  , "InternalServerError"
  ]

directions = [ "North"
             , "East"
             , "South"
             , "West"
             ]

short = [1, 2, 3]

t       = (1, True)
ignored = ( "InvalidStatusCode"
          , "MissingContentHeader"
          )


echo = do name <- getLine
          putStrLn name

greet = do
  putStr "How is your name? "
  name <- getLine
  putStrLn ("Hello " ++ name ++ "!")


take m ys               = case (m,ys) of
                            (0,_)       ->  []
                            (_,[])      ->  []
                            (n,x:xs)    ->  x : take (n-1) xs




f x = g (if x then 0 else 1) 42

g x y = x+y

foo = if True
        then 1
        else 2

{-
f x y z | x == y    = z
        | otherwise = z + 1

g x y z
  | x == y && not z = 1
  | otherwise       = 0

and True True = True
and _    _    = False

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs
-}



area :: Int -- width
     -> Int -- height
     -> Int -- area
area x y = x * y

{- 
data Bit = Zero | One

data Tree a =
    Leaf
  | Branch a (Tree a) (Tree a)

data Person = Person
    { firstName :: String
    , lastName  :: String
    , age       :: Int
    }
-}

test = ["string", "string1", "string4"]

-- Curry's solution to the "diamond" problem of the
-- Prolog programming contest at JICSLP'98 in Manchester


diamond n = lineloop1 1 1 >> lineloop2 1 (n*n-n+2)  where

 lineloop1 i j = if i<=n then line j i >> lineloop1 (i+1) (j+n) else done

 lineloop2 i j = if i<n then line j (n-i) >> lineloop2 (i+1) (j+1) else done

 line s e = tab((n-e)*(size(n*n)+1)) >> lineloop 1 s
   where
      lineloop i t =
             if i<=e
             then putValue t >> tab (size(n*n)+1) >> lineloop (i+1) (t-n+1)
             else putChar '\n'

      putValue v = tab((size(n*n)+1)-size(v)) >> putStr (show v)


tab n = if n==0 then done else putChar ' ' >> tab (n-1)

-- number of characters for the string representation of a number:
size n = if n<10 then 1 else size (n `div` 10) + 1

