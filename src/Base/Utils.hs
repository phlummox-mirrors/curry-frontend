{- |
    Module      :  $Header$
    Description :  Auxiliary functions
    Copyright   :  (c) 2001 - 2003 Wolfgang Lux
                       2011 - 2015 Björn Peemöler
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The module Utils provides a few simple functions that are
   commonly used in the compiler, but not implemented in the Haskell
   Prelude or standard library.
-}

module Base.Utils
  ( (++!), foldr2, mapAccumM, findDouble, concatMapM, findMultiples
  ) where

import Data.List (partition)

infixr 5 ++!

-- The function (++!) is variant of the list concatenation operator (++)
-- that ignores the second argument if the first is a non-empty list.
-- When lists are used to encode non-determinism in Haskell,
-- this operator has the same effect as the cut operator in Prolog,
-- hence the ! in the name.

(++!) :: [a] -> [a] -> [a]
xs ++! ys = if null xs then ys else xs

-- Fold operations with two arguments lists can be defined using
-- zip and foldl or foldr, resp. Our definitions are unfolded for
-- efficiency reasons.
-- foldl2 :: (a -> b -> c -> a) -> a -> [b] -> [c] -> a
-- foldl2 _ z []       _        = z
-- foldl2 _ z _        []       = z
-- foldl2 f z (x : xs) (y : ys) = foldl2 f (f z x y) xs ys

foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 _ z []       _        = z
foldr2 _ z _        []       = z
foldr2 f z (x : xs) (y : ys) = f x y (foldr2 f z xs ys)

-- The function 'mapAccumM' is a generalization of mapAccumL to monads
-- like foldM is for foldl.
mapAccumM :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])
mapAccumM _ s []       = return (s, [])
mapAccumM f s (x : xs) = do
  (s' , y ) <- f s x
  (s'', ys) <- mapAccumM f s' xs
  return (s'', y : ys)

-- The function 'concatMapM' is a generalization of concatMap to monads
-- like foldM is for foldl.
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = mapM f xs >>= return . concat

-- The function 'findDouble' checks whether a list of entities is linear,
-- i.e., if every entity in the list occurs only once. If it is non-linear,
-- the first offending object is returned.
findDouble :: Eq a => [a] -> Maybe a
findDouble []   = Nothing
findDouble (x : xs)
  | x `elem` xs = Just x
  | otherwise   = findDouble xs

findMultiples :: Eq a => [a] -> [[a]]
findMultiples []       = []
findMultiples (x : xs)
  | null same = multiples
  | otherwise = (x : same) : multiples
  where (same, other) = partition (==x) xs
        multiples     = findMultiples other
