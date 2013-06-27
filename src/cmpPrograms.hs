
module Main where

import System.Exit
import System.Environment
import Curry.ExtendedFlat.Type

import Curry.ExtendedFlat.Equality

fromJust' :: String -> IO (Maybe a) -> IO a
fromJust' err m = do
  val <- m 
  case val of 
    Nothing -> 
      error ("\n\n\n=========\nerror: fromJust'!\n" ++ err ++ "\n=========\n\n\n")
    Just x -> return x  

main :: IO ()
main = do
  args <- getArgs
  putStr ("Comparing \"" ++ (args !! 0) ++ "\" and \"" ++ (args !! 1) ++ "\": ")
  p1 <- fromJust' (args !! 0) $ readFlat (args !! 0)
  p2 <- fromJust' (args !! 1) $ readFlat (args !! 1)
  
  case progsEqual p1 p2 of
    (True, _) -> do putStrLn "Equal"; exitSuccess
    (False, cause) -> do 
      putStrLn ("Not equal, " ++ {-show (args !! 0) ++ -}"cause: " ++ cause)
      exitFailure
  
    
