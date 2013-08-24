


import Prelude ()
import TCPrelude

import Assertion

infixl 7 :*:
infixl 6 :+:

data Tree a = Node (Tree a) a (Tree a) | Leaf a | Empty
  deriving Show

test1 = show (Leaf 1)
test2 = show (Node (Leaf 1) 2 (Leaf 3))
test3 = show (Node (Leaf 1) 2 (Node (Leaf 3) 4 (Leaf 5)))
test4 = show (Empty :: Tree Int)
test5 = show (Node Empty 2 (Leaf 1))
test6 = show [Leaf 1, Node Empty 3 (Leaf 2)]
test7 = show (Leaf 1, Leaf 3)

data Arith = Arith :*: Arith | Arith :+: Arith | Val Int
  deriving Show

test8 = show (Val 1 :+: Val 2)
test9 = show (Val 1 :+: Val 3 :+: Val 3)
test10 = show (Val 1 :+: Val 3 :+: Val 3 :+: Val 4)
test10b = show (Val 1 :+: (Val 2 :+: (Val 3 :+: Val 4)))

test11 = show (Val 1 :+: Val 2 :*: Val 3)
test12 = show ((Val 1 :+: Val 2) :*: Val 3)
test13 = show ((Val 1 :+: Val 2 :*: Val 3) :*: Val 4)
test14 = show ((Val 1 :+: Val 2 :*: Val 3) :*: (Val 4 :+: Val 5))

data T a = T (S a) (S a)
  deriving Show

data S a = S a
  deriving Show

test15 = show (T (S 1) (S 2))

allTests = sequenceIO $ map putStrLn
  [ test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test10b
  , test11, test12, test13, test14, test15]


  
test1' = test1 == "Leaf 1"
test2' = test2 == "Node (Leaf 1) 2 (Leaf 3)"
test3' = test3 == "Node (Leaf 1) 2 (Node (Leaf 3) 4 (Leaf 5))"
test4' = test4 == "Empty"
test5' = test5 == "Node Empty 2 (Leaf 1)"
test6' = test6 == "[Leaf 1,Node Empty 3 (Leaf 2)]"
test7' = test7 == "(Leaf 1,Leaf 3)"
test8' = test8 == "Val 1 :+: Val 2"
test9' = test9 == "(Val 1 :+: Val 3) :+: Val 3"
test10' = test10 == "((Val 1 :+: Val 3) :+: Val 3) :+: Val 4"
test10b' = test10b == "Val 1 :+: (Val 2 :+: (Val 3 :+: Val 4))"
test11' = test11 == "Val 1 :+: Val 2 :*: Val 3"
test12' = test12 == "(Val 1 :+: Val 2) :*: Val 3"
test13' = test13 == "(Val 1 :+: Val 2 :*: Val 3) :*: Val 4"
test14' = test14 == "(Val 1 :+: Val 2 :*: Val 3) :*: (Val 4 :+: Val 5)"
test15' = test15 == "T (S 1) (S 2)"

allTests' =
  [ test1', test2', test3', test4', test5', test6', test7', test8', test9', test10', test10b'
  , test11', test12', test13', test14', test15']

allCorrect = and allTests'


test = assertTrue "allCorrect" allCorrect

