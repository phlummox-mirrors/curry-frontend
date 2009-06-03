module CurrySubdir where

import Directory
import System.Time (ClockTime)
import Control.Monad (when)

-- some definitions from PathUtils

pathSep :: Char
pathSep = '/'

curDirPath :: FilePath
curDirPath = "."

--The function breakLast is similar to the standard
--break function, except that it splits the argument list at
--the last position for which the predicate returns \texttt{True}.

breakLast :: (a -> Bool) -> [a] -> ([a],[a])
breakLast p xs =
  case break p xs of
    (prefix,[]) -> (prefix,[])
    (prefix,x:suffix)
      | null suffix' -> (prefix,x:suffix)
      | otherwise -> (prefix ++ x:prefix',suffix')
      where (prefix',suffix') = breakLast p suffix

canonPath :: FilePath -> FilePath
canonPath "" = ""
canonPath (c:cs) =
  c : if c == pathSep then canon (dropWhile (pathSep ==) cs) else canon cs
  where canon "" = ""
        canon (c:cs)
          | c == pathSep = if null cs' then "" else c : canon cs'
          | otherwise = c : canon cs
          where cs' = dropWhile (pathSep ==) cs

--When we split a path into its basename and directory we will make
--sure that the basename does not contain any path separators.
 
dirname, basename :: FilePath -> FilePath
dirname = fst . splitPath . canonPath
basename = snd . splitPath . canonPath

splitPath :: FilePath -> (FilePath,FilePath)
splitPath path =
  case breakLast (pathSep ==) path of
    (dirname,"") -> (".",path)
    (dirname,_:basename) ->
      (if null dirname then [pathSep] else dirname,basename)


--The sub directory to hide files in:

currySubdir :: String 
currySubdir = ".curry"

addCurrySubdir :: String -> String
addCurrySubdir fn = dirname fn++pathSep:currySubdir
                              ++pathSep:basename fn


--write a file to curry subdirectory

writeModule :: String -> String -> IO ()
writeModule fileName contents = do
  --writeFile fileName contents
  let subdir = dirname fileName++pathSep:currySubdir
  ex <- doesDirectoryExist subdir
  when (not ex) (createDirectory subdir)
  writeFile (addCurrySubdir fileName) contents

-- doe things with file in subdir

onExistingFileDo :: (String -> IO a) -> String -> IO a
onExistingFileDo act filename = do
  ex <- doesFileExist filename
  if ex then act filename 
    else do
      let filename' = addCurrySubdir filename
      act filename'

readModule :: String -> IO String
readModule = onExistingFileDo readFile

maybeReadModule :: String -> IO (Maybe String)
maybeReadModule filename = 
  catch (readModule filename >>= return . Just) (\_ -> return Nothing)

doesModuleExist :: String -> IO Bool
doesModuleExist = onExistingFileDo doesFileExist

getModuleModTime :: String -> IO ClockTime
getModuleModTime = onExistingFileDo getModificationTime