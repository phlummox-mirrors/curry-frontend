{-
  $Id: PathUtils.lhs,v 1.5 2003/05/04 16:12:35 wlux Exp $

  Copyright (c) 1999-2003, Wolfgang Lux
  See LICENSE for the full license.
-}

module PathUtils(-- re-exports from System.FilePath:
                 takeBaseName, -- replaceExtension,
                 dropExtension,
                 takeDirectory, takeExtension, 
                 pathSeparator,
                 catPath,

                 lookupModule, lookupFile, getCurryPath,
                 writeModule,readModule,
                 doesModuleExist,maybeReadModule,getModuleModTime) where

import System.FilePath
import System.Directory
import System.Time (ClockTime)

import Control.Monad (unless)

import Curry.Base.Ident
import Filenames


lookupModule :: [FilePath] -> [FilePath] -> ModuleIdent
             -> IO (Maybe FilePath)
lookupModule paths libraryPaths m
    = lookupFile ("" : paths ++ libraryPaths) moduleExts fn
      where fn = foldr1 catPath (moduleQualifiers m)

catPath :: FilePath -> FilePath -> FilePath
catPath = combine

lookupFile :: [FilePath] -> [String] -> String -> IO (Maybe FilePath)
lookupFile paths exts file = lookupFile' paths'
    where
      paths' = do p <- paths
                  e <- exts
                  let fn = p `combine` replaceExtension file e
                  [fn, inCurrySubdir fn]
      lookupFile' [] = return Nothing
      lookupFile' (fn:paths)
          = do so <- doesFileExist fn
               if so then return (Just fn) else lookupFile' paths



-- add a subdirectory to a given filename 
-- if it is not already present
--
-- inSubdir ""

inSubdir :: FilePath -> FilePath -> FilePath
inSubdir sub fn = joinPath $ add (splitDirectories fn) 
  where
    add ps@[n] = sub:ps
    add ps@[p,n] | p==sub = ps
    add (p:ps) = p:add ps

--The sub directory to hide files in:

currySubdir :: String 
currySubdir = ".curry"

inCurrySubdir :: FilePath -> FilePath
inCurrySubdir = inSubdir currySubdir

--write a file to curry subdirectory

writeModule :: FilePath -> String -> IO ()
writeModule filename contents = do
  let filename' = inCurrySubdir filename
      subdir = takeDirectory filename'
  ensureDirectoryExists subdir
  writeFile filename' contents

ensureDirectoryExists :: FilePath -> IO ()
ensureDirectoryExists dir
    = do ex <- doesDirectoryExist dir
         unless ex (createDirectory dir)

-- do things with file in subdir

onExistingFileDo :: (FilePath -> IO a) -> FilePath -> IO a
onExistingFileDo act filename = do
  ex <- doesFileExist filename
  if ex then act filename 
        else act $ inCurrySubdir filename

readModule :: FilePath -> IO String
readModule = onExistingFileDo readFile

maybeReadModule :: FilePath -> IO (Maybe String)
maybeReadModule filename = 
  catch (readModule filename >>= return . Just) (\_ -> return Nothing)

doesModuleExist :: FilePath -> IO Bool
doesModuleExist = onExistingFileDo doesFileExist

getModuleModTime :: FilePath -> IO ClockTime
getModuleModTime = onExistingFileDo getModificationTime


{-
  The function \verb|getCurryPath| searches in predefined paths
  for the corresponding \texttt{.curry} or \texttt{.lcurry} file, 
  if the given file name has no extension.
-}
getCurryPath :: [FilePath] -> FilePath -> IO (Maybe FilePath)
getCurryPath paths fn = lookupFile filepaths exts fn
    where
      filepaths = "":paths'
      fnext = takeExtension fn
      exts | null fnext = sourceExts
           | otherwise  = [fnext]
      paths' | pathSeparator `elem` fn = []
             | otherwise               = paths

