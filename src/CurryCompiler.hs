-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- CurryCompiler - Compiles Curry programs. Note, that the compiler does not
--                 resolve import dependencies, i.e. the compiler needs
--                 FlatInterface files of all imported modules.
--                
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module CurryCompiler (compileCurry) where

import CurryCompilerOpts
import qualified Options as Opts
import Modules
import System
import IO


-------------------------------------------------------------------------------

compileCurry :: Options -> FilePath -> IO ()
compileCurry options file
   = compileModule opts file
 where
 opts = Opts.defaultOptions{ Opts.importPath = importPaths options,
			     Opts.output = output options,
			     Opts.noInterface = noInterface options,
			     Opts.flatCurry = flat options,
			     Opts.flatXML = flatXml options,
			     Opts.abstract = abstract options,
			     Opts.untypedAbstract = untypedAbstract options,
			     Opts.dump = dump options
			   }


-------------------------------------------------------------------------------
-- Error handling

-- Prints an error message on 'stderr'
putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

-- Prints a list of error messages on 'stderr'
putErrsLn :: [String] -> IO ()
putErrsLn = mapM_ putErrLn

-- Prints a list of error messages on 'stderr' and aborts the program
abortWith :: [String] -> IO ()
abortWith errs = putErrsLn errs >> exitWith (ExitFailure 1)

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------