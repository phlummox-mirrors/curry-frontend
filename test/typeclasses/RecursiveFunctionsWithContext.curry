{-# OPTIONS_CYMAKE -X TypeClassExtensions #-}

module Test1 where

test1 :: Ord a => [a] -> Bool
test1 [x,y] = test2 x || test3 y || x < y
test1 [x] = False

test2 :: Ord a => a -> Bool
test2 x = test1 [x]
 
test3 :: Ord a => a -> Bool
test3 x = test2 [x]
