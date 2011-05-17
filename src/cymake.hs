{- |cymake - The Curry builder

    Command line tool for generating Curry representations (e.g. FlatCurry,
    AbstractCurry) for a Curry source file including all imported modules.

    September 2005, Martin Engelke (men@informatik.uni-kiel.de)
    May 2011, Bjoern Peemoeller (bjp@informatik.uni-kiel.de)
-}
module Main (main) where

import CurryBuilder (buildCurry)
import CompilerOpts (Options (..), compilerOpts, usage)
import Files.CymakePath (cymakeGreeting)
import Html.CurryHtml (source2html)
import Messages (putErrsLn, abortWith)

-- |The command line tool cymake
main :: IO ()
main = compilerOpts >>= cymake

-- |Check the command line arguments and invoke the curry builder
cymake :: (String, Options, [String], [String]) -> IO ()
cymake (prog, opts, files, errs)
  | optHelp opts    = printUsage prog
  | optVersion opts = printVersion
  | null files      = printUsage prog
  | not (null errs) = badUsage prog errs
  | optHtml opts    = mapM_ (source2html opts) files
  | otherwise       = mapM_ (buildCurry  opts) files

-- |Print the program greeting
printVersion :: IO ()
printVersion = putStrLn cymakeGreeting

-- |Print the usage information of the command line tool.
printUsage :: String -> IO ()
printUsage prog = putStrLn $ usage prog

-- |Print errors and abort execution
badUsage :: String -> [String] -> IO ()
badUsage prog errs = do
  putErrsLn $ map (\ err -> prog ++ ": " ++ err) errs
  abortWith ["Try '" ++ prog ++ " --help' for more information"]
