-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- A small configuration program for generating text files by replacing
-- strings within pattern files
--
--
-- January 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--

import Time
import System
import Directory


-------------------------------------------------------------------------------

-- Usage:
--    config <filename>
--
-- Generates the file <filename> by modifying the pattern file
-- "<filename>-pattern". It replaces the following string in
-- the pattern file:
--      - "%BUILD_DIR%" with the path from the environment variable MCC_PATH
--      - "%BUILD_DATE%" with the actual date
--
main :: IO ()
main
   = do name <- getFilename
        date <- getDate
        path <- getPath
        generateExec date path name


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Executive function of 'main' (see above)
--
-- Call:
--      generateExec <string containing the date>
--                   <string containing the path to MCC>
--                   <name of the pattern file without suffix "-pattern">
-- 
generateExec :: String -> String -> String -> IO ()
generateExec date path name
   = do putStrLn ("Generating file \"" ++ name ++ "\"...")
        pattfile <- readFile (name ++ "-pattern")
	writeFile name (replace [("%BUILD_DIR%",  path),
				 ("%BUILD_DATE%", date)]
			        pattfile)
	putStrLn "...done"


-------------------------------------------------------------------------------

-- A small function for replacing parts within a string.
--
-- Call:
--      replace <list of pairs (old string, new string)>
--              <string where to perform the replacements>
--
replace :: [(String,String)] -> String -> String
replace reps [] = []
replace reps (c:cs)
   = maybe (c:(replace reps cs))
           (\ (old, new) -> new ++ (replace reps (drop (length old) (c:cs))))
           (p_getReplacement reps (c:cs))
 where
 p_getReplacement []               text = Nothing
 p_getReplacement ((old,new):reps) text
    | isPrefix old text = Just (old, new)
    | otherwise         = p_getReplacement reps text


-------------------------------------------------------------------------------
-- Some functions for getting several information like command line arguments
-- (filename), actual date, path to MCC (from the environment variable
-- MCC_PATH).

getFilename :: IO String
getFilename
   = do args <- getArgs
        if null args
	   then error "config: missing filename"
           else return (head args)


getDate :: IO String
getDate
   = do time <- getClockTime
        date <- toCalendarTime time
        return (calendarTimeToString date)


getPath :: IO String
getPath = getEnv "MCC_PATH"


-- Prints a reasond and exits the program if the exit code
-- is not 'ExitSuccess'
checkExitCode :: ExitCode -> String -> IO ()
checkExitCode exitcode reason
   = case exitcode of
       ExitSuccess -> putStr ""
       _           -> putStrLn reason >> exitWith exitcode


-------------------------------------------------------------------------------

-- Returns 'True' if the first string argument is a prefix of the second
isPrefix :: String -> String -> Bool
isPrefix []     []     = True
isPrefix (x:xs) []     = False
isPrefix []     (y:ys) = True
isPrefix (x:xs) (y:ys) = x == y && isPrefix xs ys


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
