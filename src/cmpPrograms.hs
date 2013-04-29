
module Main where

import System.Exit
import System.Environment
import Data.Maybe
import Curry.ExtendedFlat.Type

import Curry.ExtendedFlat.Equality
import Control.Monad

main :: IO ()
main = do
  args <- getArgs
  -- print ("Comparing " ++ (args !! 0) ++ " " ++ (args !! 1))
  p1 <- liftM fromJust $ readFlat (args !! 0)
  p2 <- liftM fromJust $ readFlat (args !! 1)
  
  case progsEqual p1 p2 of
    True -> do putStrLn "Equal"; exitSuccess
    False -> do putStrLn ("Not equal: " ++ show (args !! 0)); exitFailure
  
    
