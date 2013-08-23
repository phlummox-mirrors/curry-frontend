
-- data Arith = Arith :*: Arith | Int :+: Int | Int

import Prelude ()
import TCPrelude

data Tree a = Node (Tree a) a (Tree a) | Leaf a | Empty
  deriving Show

test1 = show (Leaf 1)
test2 = show (Node (Leaf 1) 2 (Leaf 3))
test3 = show (Node (Leaf 1) 2 (Node (Leaf 3) 4 (Leaf 5)))
test4 = show (Empty :: Tree Int)
test5 = show (Node Empty 2 (Leaf 1))

allTests = sequenceIO $ map print [test1, test2, test3, test4, test5]

