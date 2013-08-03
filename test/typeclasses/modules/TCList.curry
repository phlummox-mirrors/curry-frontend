------------------------------------------------------------------------------
--- Library with some useful operations on lists, using type classes
---
--- @author Michael Hanus, Bjoern Peemoeller
--- @version August 2013
------------------------------------------------------------------------------

module TCList
  ( elemIndex, elemIndices, find, findIndex, findIndices
  , nub, nubBy, delete, deleteBy, (\\), union, intersect
  , intersperse, intercalate, transpose, permutations, partition
  , group, groupBy, splitOn, split, inits, tails, replace
  , isPrefixOf, isSuffixOf, isInfixOf
  , sortBy, insertBy, sort, insert
  , last, init
  , sum, product, maximum, minimum
  , scanl, scanl1, scanr, scanr1
  , mapAccumL, mapAccumR
  , cycle, unfoldr
  ) where

import Prelude ()
import TCPrelude

-- import functions from List that don't need type classes
import List(find, findIndex, findIndices, nubBy, deleteBy, intersperse, intercalate
           , transpose, permutations, partition, groupBy, split, inits, tails
           , replace, sortBy, insertBy, last, init, sum, product, scanl, scanl1
           , scanr, scanr1, mapAccumL, mapAccumR, cycle, unfoldr)
  
import Maybe (listToMaybe)

infix 5 \\

--- Returns the index `i` of the first occurrence of an element in a list
--- as `(Just i)`, otherwise `Nothing` is returned.
elemIndex               :: Eq a => a -> [a] -> Maybe Int
elemIndex x              = findIndex (x ==)

--- Returns the list of indices of occurrences of an element in a list.
elemIndices             :: Eq a => a -> [a] -> [Int]
elemIndices x            = findIndices (x ==)

--- Removes all duplicates in the argument list.
nub                   :: Eq a => [a] -> [a]
nub xs                 = nubBy (==) xs

--- Deletes the first occurrence of an element in a list.
delete                :: Eq a => a -> [a] -> [a]
delete                 = deleteBy (==)

--- Computes the difference of two lists.
--- @param xs - a list
--- @param ys - a list
--- @return the list where the first occurrence of each element of
---         `ys` has been removed from `xs`
(\\) :: Eq a => [a] -> [a] -> [a]
xs \\ ys = foldl (flip delete) xs ys

--- Computes the union of two lists.
union                 :: Eq a => [a] -> [a] -> [a]
union []     ys        = ys
union (x:xs) ys        = if x `elem` ys then union xs ys
                                        else x : union xs ys

--- Computes the intersection of two lists.
intersect             :: Eq a => [a] -> [a] -> [a]
intersect []     _     = []
intersect (x:xs) ys    = if x `elem` ys then x : intersect xs ys
                                        else intersect xs ys



--- Splits the list argument into a list of lists of equal adjacent
--- elements.
---
--- Example: `(group [1,2,2,3,3,3,4]) = [[1],[2,2],[3,3,3],[4]]`
group :: Eq a => [a] -> [[a]]
group = groupBy (==)



--- Breaks a the second lsit argument into pieces separated by the first
--- list argument, consuming the delimiter. An empty delimiter is
--- invalid, and will cause an error to be raised.
splitOn :: Eq a => [a] -> [a] -> [[a]]
splitOn []          _  = error "splitOn called with an empty pattern"
splitOn [x]         xs = split (x ==) xs
splitOn sep@(_:_:_) xs = go xs
  where go []                           = [[]]
        go l@(y:ys) | sep `isPrefixOf` l = [] : go (drop len l)
                    | otherwise         = let (zs:zss) = go ys in (y:zs):zss
        len = length sep






--- Checks whether a list is a prefix of another.
--- @param xs - a list
--- @param ys - a list
--- @return `True` if `xs` is a prefix of `ys`
isPrefixOf :: Eq a => [a] -> [a] -> Bool
isPrefixOf [] _ = True
isPrefixOf (_:_) [] = False
isPrefixOf (x:xs) (y:ys) = x==y && (isPrefixOf xs ys)

--- Checks whether a list is a suffix of another.
--- @param xs - a list
--- @param ys - a list
--- @return `True` if `xs` is a suffix of `ys`
isSuffixOf :: Eq a => [a] -> [a] -> Bool
isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

--- Checks whether a list is contained in another.
--- @param xs - a list
--- @param ys - a list
--- @return True if xs is contained in ys
isInfixOf :: Eq a => [a] -> [a] -> Bool
isInfixOf xs ys = any (isPrefixOf xs) (tails ys)

--- Sorts the given list
sort :: Ord a => [a] -> [a]
sort = foldr insert []

--- Inserts an element in the list according to the ordering
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]

insert x (y:ys) = if x <= y
                    then x : y : ys
                    else y : insertBy x ys

--- Returns the maximum of a non-empty list.
maximum :: Ord a => [a] -> a
maximum xs@(_:_) =  foldl1 max xs

--- Returns the minimum of a non-empty list.
minimum :: Ord a => [a] -> a
minimum xs@(_:_) =  foldl1 max xs


