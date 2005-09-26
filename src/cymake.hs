-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- cymake - The Curry builder
--
--          Command line tool for generating Curry representations (e.g.
--          FlatCurry, AbstractCurry) for a Curry source file including
--          all imported modules.
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--

import GetOpt
import CurryBuilder
import CurryBuilderOpts
import Variables
import System
import Maybe
import IO


-------------------------------------------------------------------------------

-- The command line tool.
main :: IO ()
main = do prog    <- getProgName
	  args    <- getArgs
	  imports <- getCurryImports
	  cymake prog args imports


-------------------------------------------------------------------------------

-- Checks the command line arguments and invokes the builder.
cymake :: String -> [String] -> [FilePath] -> IO ()
cymake prog args imports
   | elem Help opts = printUsage prog
   | null files     = badUsage prog ["no files"]
   | null errs'     = mapM_ (buildCurry options') files
   | otherwise      = badUsage prog errs
 where
 (opts, files, errs) = getOpt Permute options args
 options' = foldr selectOption defaultOpts{ libPaths = imports } opts
 errs'    = errs ++ check options' files


-- Prints usage information of the command line tool.
printUsage :: String -> IO ()
printUsage prog
   = do putStrLn (usageInfo header options)
	exitWith ExitSuccess
 where
 header = "usage: " ++ prog ++ " [OPTION] ... MODULE ..."


-- Prints errors
badUsage :: String -> [String] -> IO ()
badUsage prog errs
   = do mapM (\err -> putErrLn (prog ++ ": " ++ err)) errs
	abortWith ["Try '" ++ prog ++ " -" ++ "-help' for more information"]


-- Checks options and files.
check :: Options -> [String] -> [String]
check opts files
   | null files 
     = ["no files"]
   | isJust (output opts) && length files > 1
     = ["cannot specify -o with multiple targets"]
   | otherwise
     = []


-------------------------------------------------------------------------------
-- Error handling

-- Prints an error message on 'stderr'
putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

-- Prints a list of error messages on 'stderr'
putErrsLn :: [String] -> IO ()
putErrsLn = mapM_ putErrLn

-- Prints a list of error messages on 'stderr' and aborts the program
abortWith :: [String] -> IO a
abortWith errs = putErrsLn errs >> exitWith (ExitFailure 1)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
