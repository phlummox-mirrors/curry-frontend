{- |cymake - The Curry builder

    Command line tool for generating Curry representations (e.g. FlatCurry,
    AbstractCurry) for a Curry source file including all imported modules.

    September 2005, Martin Engelke (men@informatik.uni-kiel.de)
    May 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
-}
module Main (main) where

import CurryBuilder (buildCurry)
import CurryCompilerOpts (Options (..), compilerOpts, usage)
import Files.CymakePath (cymakeGreeting)
import Html.CurryHtml (source2html)
import Messages (putErrsLn, abortWith)

-- |The command line tool cymake
main :: IO ()
main = compilerOpts >>= cymake

-- |Check the command line arguments and invoke the curry builder
cymake :: (String, Options, [String], [String]) -> IO ()
cymake (prog, opts, files, errs)
  | help opts       = printUsage prog
  | version opts    = printVersion
  | null files      = printUsage prog
  | not (null errs) = badUsage prog errs
  | html opts       = mapM_ (source2html opts) files
  | otherwise       = mapM_ (buildCurry opts') files
  where
    opts' = if or [ flat opts, flatXml opts, abstract opts
                  , untypedAbstract opts, parseOnly opts]
                then  opts
                else  opts { flat = True }

-- ---------------------------------------------------------------------------

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
