-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
--  Variables - Defines some system values and functions for the frontend
--              (e.g. paths, names etc.)
--
--  September 2005,
--  Martin Engelke (men@informatik.uni-kiel.de)
--
module Variables(getCurryImports) where

import PathUtils 
import System

-------------------------------------------------------------------------------

-- Environment variables containing paths to standard imports
importVars = ["CURRYPATH",
	      "PAKCSLIBPATH"]


-------------------------------------------------------------------------------

-- Returns the paths to the standard imports
getCurryImports :: IO [FilePath]
getCurryImports
   = do imps <- mapM sureGetEnv importVars
	return (concatMap pathList imps)


-------------------------------------------------------------------------------

-- Returns the value of an environment variable, if it exists, otherwise an
-- empty string.
sureGetEnv :: String -> IO String
sureGetEnv env = catch (getEnv env) (const (return ""))


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
