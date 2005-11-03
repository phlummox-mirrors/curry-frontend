-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- CurryBuilder - Generates Curry representations for a Curry source file
--                including all imported modules.
--
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module CurryBuilder (buildCurry) where

import CurryBuilderOpts
import CurryCompiler
import qualified CurryCompilerOpts as COpts
import CurryDeps
import Ident
import PathUtils
import Env
import System
import Directory
import Time
import Monad
import Maybe
import List
import IO


-------------------------------------------------------------------------------

-- Compiles the Curry program 'file' including all imported modules, depending
-- on the options 'options'. The compilation was successful, if the returned
-- list is empty, otherwise it contains error messages.
buildCurry :: Options -> FilePath -> IO ()
buildCurry options file
   = do let paths = union (importPaths options) (libPaths options)
	file'          <- getSourcePath paths file
	(cfile, errs1) <- return (maybe ("", [missingModule file])
			                (\f -> (f,[]))
				        file')
	unless (null errs1) (abortWith errs1)
	(deps, errs2) <- genDeps paths cfile
	unless (null errs2) (abortWith errs2)
	makeCurry options deps cfile


-------------------------------------------------------------------------------

makeCurry :: Options -> [(ModuleIdent,Source)] -> FilePath -> IO ()
makeCurry options deps file
   = do mapM_ (compile . snd) deps
 where
 compile (Source file' mods)
    | rootname file == rootname file'
      = if (null (dump options))
	then smake (targetNames file')
                   (file':catMaybes (map flatInterface mods))
		   (unless (noVerb options)
		           (putStrLn ("generating " 
				      ++ (head (targetNames file')) 
				      ++ " ..."))
		    >> compileCurry (compOpts False) file')
	else unless (noVerb options)
	            (putStrLn ("generating " 
			       ++ (head (targetNames file')) 
			       ++ " ..."))
             >> compileCurry (compOpts False) file'
    | otherwise
      = smake [flatName file', flatIntName file']
	      (file':catMaybes (map flatInterface mods))
	      (unless (noVerb options) 
	              (putStrLn ("compiling " ++ file' ++ " ..."))
	       >> compileCurry (compOpts True) file')
	  
 compile _ = return ()

 targetNames fn | flat options            = [flatName fn, flatIntName fn]
		| flatXml options         = [xmlName fn]
		| abstract options        = [acyName fn]
		| untypedAbstract options = [uacyName fn]
		| otherwise               = [flatName fn, flatIntName fn]

 flatInterface mod 
    = case (lookup mod deps) of
        Just (Source file _)  -> Just (flatIntName (rootname file))
	Just (Interface file) -> Just (flatIntName (rootname file))
	_                     -> Nothing

 compOpts isImport
    | isImport 
      = COpts.defaultOpts 
	   {COpts.importPaths = importPaths options ++ libPaths options,
	    COpts.output = output options,
	    COpts.noVerb = noVerb options,
	    COpts.noWarn = noWarn options,
	    COpts.flat = True,
	    COpts.flatXml = False,
	    COpts.abstract = False,
	    COpts.untypedAbstract = False,
	    COpts.dump = []
	   }
    | otherwise
      = COpts.defaultOpts 
	   {COpts.importPaths = importPaths options ++ libPaths options,
	    COpts.output = output options,
	    COpts.noVerb = noVerb options,
	    COpts.noWarn = noWarn options,
	    COpts.flat = flat options,
	    COpts.flatXml = flatXml options,
	    COpts.abstract = abstract options,
	    COpts.untypedAbstract = untypedAbstract options,
	    COpts.dump = dump options
	   }
			 

-------------------------------------------------------------------------------

-- Searches in 'paths' for the corresponding Curry file of 'fn' and returns
-- the complete path if it exist. The filename 'fn' doesn't need one of the 
-- Curry file extensions ".curry" or ".lcurry"
getSourcePath :: [FilePath] -> FilePath -> IO (Maybe FilePath)
getSourcePath paths file = getCurryPath paths [] file


-- Computes a dependency list for the Curry file 'file' (such a list
-- usualy starts with the prelude and ends with 'file'). The result 
-- is a tuple containing an association list (type [(ModuleIdent,Source)]; 
-- see module "CurryDeps") and a list of error messages.
genDeps :: [FilePath] -> FilePath
	   -> IO ([(ModuleIdent,Source)], [String])
genDeps paths file
   = fmap (flattenDeps . sortDeps) (deps paths [] emptyEnv file)


-------------------------------------------------------------------------------
-- A simple make function

--
smake :: [FilePath] -> [FilePath] -> IO () -> IO ()
smake dests deps cmd
   = do destTimes <- getDestTimes dests
	depTimes  <- getDepTimes deps
	make destTimes depTimes
 where
 make destTimes depTimes
    | (length destTimes) < (length dests) 
      = catch cmd (\err -> abortWith [show err]) 
    | null depTimes 
      = abortWith ["unknown dependencies"]
    | outOfDate destTimes depTimes
      = catch cmd (\err -> abortWith [show err])
    | otherwise
      = return ()

--
getDestTimes :: [FilePath] -> IO [ClockTime]
getDestTimes [] = return []
getDestTimes (file:files)
   = catch (do time  <- getModificationTime file
	       times <- getDestTimes files
	       return (time:times))
           (const (getDestTimes files))

--
getDepTimes :: [String] -> IO [ClockTime]
getDepTimes [] = return []
getDepTimes (file:files)
   = catch (do time  <- getModificationTime file
	       times <- getDepTimes files
	       return (time:times))
           (\err -> abortWith [show err])

--
outOfDate :: [ClockTime] -> [ClockTime] -> Bool
outOfDate tgtimes dptimes = or (map (\t -> or (map ((<) t) dptimes)) tgtimes)


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


-- Error messages

missingModule :: FilePath -> String
missingModule file = "Error: missing module \"" ++ file ++ "\""

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------