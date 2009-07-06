module Filenames(module Filenames,
                     
                ) where

import System.FilePath

-- Various filename extensions



curryExt, lcurryExt, icurryExt, oExt :: String
curryExt = ".curry"

lcurryExt = ".lcurry"

icurryExt = ".icurry"

flatExt = ".fcy"

flatIntExt = ".fint"
-- fintExt = ".fint"

xmlExt = "_flat.xml"

acyExt = ".acy"

uacyExt = ".uacy"

sourceRepExt = ".cy"

oExt = ".o"

debugExt = ".d.o"

sourceExts, moduleExts, objectExts :: [String]
sourceExts = [curryExt,lcurryExt]
moduleExts = sourceExts ++ [icurryExt]
objectExts = [oExt]

{-
  The following functions compute the name of the target file (e.g.
  interface file, flat curry file etc.)
  for a source module. Note that
  output files are always created in the same directory as the source
  file.
-}

interfName :: FilePath -> FilePath
interfName sfn = replaceExtension sfn icurryExt


flatName :: FilePath -> FilePath
flatName fn = replaceExtension fn flatExt

flatIntName :: FilePath -> FilePath
flatIntName fn = replaceExtension fn flatIntExt

xmlName :: FilePath -> FilePath
xmlName fn = replaceExtension fn xmlExt

acyName :: FilePath -> FilePath
acyName fn = replaceExtension fn acyExt

uacyName :: FilePath -> FilePath
uacyName fn = replaceExtension fn uacyExt

sourceRepName :: FilePath -> FilePath
sourceRepName fn = replaceExtension fn sourceRepExt

objectName :: Bool -> FilePath -> FilePath
objectName debug = name (if debug then debugExt else oExt)
    where name ext fn = replaceExtension fn ext
