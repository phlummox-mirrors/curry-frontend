{- |
    Module      :  $Header$
    Description :  Main module
    Copyright   :  (c) 2005, Martin Engelke (men@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Command line tool for generating Curry representations (e.g. FlatCurry,
    AbstractCurry) for a Curry source file including all imported modules.
-}
module Main (main) where

import Base.Messages (putErrsLn, abortWith)
import Files.CymakePath (cymakeGreeting)
import Html.CurryHtml (source2html)

import CurryBuilder (buildCurry)
import CompilerOpts (Options (..), compilerOpts, usage)

-- |The command line tool cymake
main :: IO ()
main = compilerOpts >>= cymake

-- |Invoke the curry builder w.r.t the command line arguments
cymake :: (String, Options, [String], [String]) -> IO ()
cymake (prog, opts, files, errs)
  | optHelp opts    = printUsage prog
  | optVersion opts = printVersion
  | null files      = printUsage prog
  | not $ null errs = badUsage prog errs
  | optHtml opts    = mapM_ (source2html opts) files
  | otherwise       = mapM_ (buildCurry  opts) files

-- |Print the program greeting
printVersion :: IO ()
printVersion = putStrLn cymakeGreeting

-- |Print the usage information of the command line tool
printUsage :: String -> IO ()
printUsage prog = putStrLn $ usage prog

-- |Print errors and abort execution on bad parameters
badUsage :: String -> [String] -> IO ()
badUsage prog errs = do
  putErrsLn $ map (\ err -> prog ++ ": " ++ err) errs
  abortWith ["Try '" ++ prog ++ " --help' for more information"]
