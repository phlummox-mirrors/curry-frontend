-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- A small configuration program for extending pattern files
--
--
-- January 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--

import Time
import System
import Directory


-------------------------------------------------------------------------------

-- Call:
--    config <filename>
--
-- Generates the file <filename> by modifying the pattern file
-- "<filename>-pattern".
--
main :: IO ()
main
   = do name <- getFilename
        date <- getDate
        path <- getPath
        generateExec date path name


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

generateExec :: String -> String -> String -> IO ()
generateExec date path name
   = do putStrLn ("Generating file \"" ++ name ++ "\"...")
        pattfile <- readFile (name ++ "-pattern")
	writeFile name (replace [("%BUILD_DIR%",  path),
				 ("%BUILD_DATE%", date)]
			        pattfile)
	--codes1 <- replace name [("%BUILD_DIR%",  path),
	--		        ("%BUILD_DATE%", date)]
	--mapM_ (flip checkExitCode ("config: 'sed-replace' failed on \"" 
        --                             ++ name ++ "\""))
        --      codes1
	--code2 <- system ("chmod 755 " ++ name)
	--checkExitCode code2 ("config: 'chmod' failed on \"" ++ name ++ "\"")
	putStrLn "...done"


-------------------------------------------------------------------------------

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


--replace :: String -> [(String, String)] -> IO [ExitCode]
--replace file replacements
--   = mapM (\(old,new) -> system ("sed -i 's/"++esc old++"/"++esc new++"/' "++file)) 
--           replacements
-- where
--   esc "" = ""
--   esc ('/':xs) = '\\':'/':esc xs
--   esc (x:xs) = x:esc xs

-------------------------------------------------------------------------------

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



checkExitCode :: ExitCode -> String -> IO ()
checkExitCode exitcode reason
   = case exitcode of
       ExitSuccess -> putStr ""
       _           -> putStrLn reason >> exitWith exitcode


-------------------------------------------------------------------------------

splitPath :: String -> [String]
splitPath path = p_splitPath "" path
 where
 p_splitPath dir [] = [reverse dir]
 p_splitPath dir (c:cs)
    | c == '/'  = (reverse dir):(p_splitPath "" cs)
    | otherwise = p_splitPath (c:dir) cs


concatDirs :: [String] -> String
concatDirs []         = []
concatDirs [dir]      = dir
concatDirs (d1:d2:ds) = d1 ++ ('/':(concatDirs (d2:ds)))


getPathFor :: String -> String -> String
getPathFor dir path
   = concatDirs ((takeWhile ((/=) dir) (splitPath path)) ++ [dir])


--
isPrefix :: String -> String -> Bool
isPrefix []     []     = True
isPrefix (x:xs) []     = False
isPrefix []     (y:ys) = True
isPrefix (x:xs) (y:ys) = x == y && isPrefix xs ys


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
