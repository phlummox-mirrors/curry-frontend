module Main ( main ) where

import TestTypeChecking

main :: IO ()
main = do
  dirsContent <- readFile "test/typeCheckTests.txt"
  let dirs = filter (/= []) $ lines dirsContent
  mapM_ checkDir (map Dir dirs) 
  







