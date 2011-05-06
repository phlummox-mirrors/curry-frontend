{- |cymake - The Curry builder

    Command line tool for generating Curry representations (e.g. FlatCurry,
    AbstractCurry) for a Curry source file including all imported modules.

    September 2005, Martin Engelke (men@informatik.uni-kiel.de)
    February 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
-}
module Main (main) where

import Data.Maybe (isJust)
import System.Environment (getArgs, getProgName)

import CurryBuilder (buildCurry)
import CurryCompilerOpts (Options (..), parseOpts, printUsage, printVersion)
import Files.CymakePath (cymakeGreeting)
import Html.CurryHtml (source2html)
import Messages (info, putErrsLn, abortWith)

-- |The command line tool cymake
main :: IO ()
main = do
  prog <- getProgName
  args <- getArgs
  cymake prog (parseOpts args)

-- |Check the command line arguments and invoke the curry builder
cymake :: String -> (Options, [String], [String]) -> IO ()
cymake prog (opts, files, errs)
  | help opts         = printUsage prog
  | version opts      = printVersion
  | not (null errs')  = badUsage prog errs'
  | html opts         = mapM_ (source2html opts) files
  | otherwise         = info opts cymakeGreeting
                        >> mapM_ (buildCurry opts') files
  where
  opts' = if or [ flat opts, flatXml opts, abstract opts
                , untypedAbstract opts, parseOnly opts]
              then  opts
              else  opts { flat = True }
  errs' = errs ++ check opts' files

-- |Print errors
badUsage :: String -> [String] -> IO ()
badUsage prog errs = do
  putErrsLn $ map (\ err -> prog ++ ": " ++ err) errs
  abortWith ["Try '" ++ prog ++ " --help' for more information"]

-- |Check options and files and return a list of error messages
check :: Options -> [String] -> [String]
check opts files
  | null files
    = ["no files"]
  | isJust (output opts) && length files > 1
    = ["cannot specify -o with multiple targets"]
  | otherwise
    = []
