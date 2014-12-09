

module BugClassMethodsAndTopLevelFuns1 
  (
  Test(..)
  ) where
    

class Test a where

  test1 :: [a] -> a
  test2 :: a -> ()
  test3 :: (a, a) -> a

