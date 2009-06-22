module CurrySubdir where

import System.FilePath
import System.Directory
import System.Time (ClockTime)
import Control.Monad (when)
import Data.List(intersperse)

-- some definitions from PathUtils

curDirPath :: FilePath
curDirPath = "."

-- divide given puth names in directories

path :: String -> [String]
path = canonPath . separateBy (==pathSeparator) 
  where
    canonPath (c:cs) = c:filter (not . null) cs

-- separate a list by separator predicate

separateBy :: (a -> Bool) -> [a] -> [[a]]
separateBy p = sep id 
  where
    sep xs [] = [xs []]
    sep xs (c:cs) = if p c then xs [] : sep id cs
                           else sep (xs . (c:)) cs

-- make canonical path from list of directories

unpath :: [String] -> String
unpath = concat . intersperse [pathSeparator]

--When we split a path into its basename and directory we will make
--sure that the basename does not contain any path separators.
 
dirname, basename :: FilePath -> FilePath
dirname  = unpath . init . path
basename = last . path

-- add a subdirectory to a given filename 
-- if it is not already present

inSubdir :: String -> String -> String
inSubdir sub fn = unpath $ add (path fn) 
  where
    add ps@[n] = sub:ps
    add ps@[p,n] | p==sub = ps
    add (p:ps) = p:add ps

--The sub directory to hide files in:

currySubdir :: String 
currySubdir = ".curry"

inCurrySubdir :: String -> String
inCurrySubdir = inSubdir currySubdir

--write a file to curry subdirectory

writeModule :: String -> String -> IO ()
writeModule filename contents = do
  --writeFile filename contents
  let filename' = inCurrySubdir filename
      subdir = dirname filename'
  ex <- doesDirectoryExist subdir
  when (not ex) (createDirectory subdir)
  writeFile filename' contents

-- do things with file in subdir

onExistingFileDo :: (String -> IO a) -> String -> IO a
onExistingFileDo act filename = do
  ex <- doesFileExist filename
  if ex then act filename 
        else act $ inCurrySubdir filename

readModule :: String -> IO String
readModule = onExistingFileDo readFile

maybeReadModule :: String -> IO (Maybe String)
maybeReadModule filename = 
  catch (readModule filename >>= return . Just) (\_ -> return Nothing)

doesModuleExist :: String -> IO Bool
doesModuleExist = onExistingFileDo doesFileExist

getModuleModTime :: String -> IO ClockTime
getModuleModTime = onExistingFileDo getModificationTime