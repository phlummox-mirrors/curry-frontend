{- |CurryBuilder - Generates Curry representations for a Curry source file
                   including all imported modules.

    September 2005, Martin Engelke (men@informatik.uni-kiel.de)
    March 2007, extensions by Sebastian Fischer (sebf@informatik.uni-kiel.de)
-}
module CurryBuilder (buildCurry, smake) where

import Control.Monad (liftM, unless)
import Data.Maybe (catMaybes, fromMaybe)
import System.Time (ClockTime)

import Curry.Base.Ident
import Curry.Files.Filenames
import Curry.Files.PathUtils ( dropExtension, doesModuleExist, getCurryPath
  , getModuleModTime, tryGetModuleModTime)

import CurryCompilerOpts (Options (..))
import CurryDeps (Source (..), flatDeps)
import Messages (status, abortWith)
import Modules (compileModule)

{- |Compile the Curry program 'file' including all imported modules,
    depending on the 'Options'. The compilation was successful if the
    returned list is empty, otherwise it contains error messages.
-}
buildCurry :: Options -> FilePath -> IO ()
buildCurry opts file = do
  file' <- getCurryPath paths file
  case file' of
    Nothing -> abortWith [missingModule file]
    Just f  -> do
      (deps, errs) <- flatDeps implicitPrelude paths [] f
      unless (null errs) (abortWith errs)
      makeCurry opts deps f
  where
    paths = importPaths opts
    implicitPrelude = not $ xNoImplicitPrelude opts
    missingModule f = "Error: missing module \"" ++ f ++ "\""

makeCurry :: Options -> [(ModuleIdent, Source)] -> FilePath -> IO ()
makeCurry opts deps1 targetFile = mapM_ (compile . snd) deps1 where

  compile (Interface _) = return ()
  compile Unknown       = return ()
  compile (Source file mods) =
      -- target file
    | dropExtension targetFile == dropExtension file = do
        flatIntfExists <- doesModuleExist (flatIntName file)
        if flatIntfExists && not (force opts) && null (dump opts)
          then smake (targetNames file)
                      (file': (catMaybes (map flatInterface mods)))
                      (generateFile file)
                      (skipFile file)
          else generateFile file
    | otherwise = do
        flatIntfExists <- doesModuleExist (flatIntName file)
        if flatIntfExists
          then smake [flatName' opts file] --[flatName file', flatIntName file']
                      (file : (catMaybes (map flatInterface mods)))
                      (compileFile file)
                      (skipFile file)
          else compileFile file

  compileFile f = do
    status opts $ "compiling " ++ f
    compileModule (compOpts True) f >> return ()

  skipFile f = status opts $ "skipping " ++ f

  generateFile f = do
    status opts $ "generating " ++ head (targetNames f)
    compileModule (compOpts False) f >> return ()

  targetNames fn
    | flat opts            = [flatName' opts fn] -- , flatIntName fn]
    | flatXml opts         = [xmlName fn]
    | abstract opts        = [acyName fn]
    | untypedAbstract opts = [uacyName fn]
    | parseOnly opts       = [fromMaybe (sourceRepName fn) (output opts)]
    | otherwise            = [flatName' opts fn] -- , flatIntName fn]

  flatInterface mod1 = case (lookup mod1 deps1) of
    Just (Source file _)  -> Just $ flatIntName file
    Just (Interface file) -> Just $ flatIntName file
    _                     -> Nothing

  compOpts isImport
    | isImport = opts
        { flat = True
        , flatXml = False
        , abstract = False
        , untypedAbstract = False
        , parseOnly = False
        , dump = []
        }
    | otherwise = opts

flatName' :: Options -> FilePath -> FilePath
flatName' opts = if extendedFlat opts then extFlatName else flatName

{- |A simple make function

    smake <destination files>
          <dependencies>
          <io action, if dependencies are newer than destination files>
          <io action, if destination files are newer than dependencies>
-}
smake :: [FilePath] -> [FilePath] -> IO a -> IO a -> IO a
smake dests deps cmd alt = do
  destTimes <- getDestTimes dests
  depTimes  <- getDepTimes deps
  abortOnError (make destTimes depTimes)
  where
  make destTimes depTimes
    | (length destTimes) < (length dests) = cmd
    | null depTimes                       = abortWith ["unknown dependencies"]
    | outOfDate destTimes depTimes        = cmd
    | otherwise                           = alt

abortOnError :: IO a -> IO a
abortOnError act = catch act (\err -> abortWith [show err])

--
getDestTimes :: [FilePath] -> IO [ClockTime]
getDestTimes = liftM catMaybes . mapM tryGetModuleModTime
-- getDestTimes [] = return []
-- getDestTimes (file:files) = catch
--   (do time  <- getModuleModTime file
--       times <- getDestTimes files
--       return (time:times))
--   (const (getDestTimes files))

--
getDepTimes :: [String] -> IO [ClockTime]
getDepTimes = mapM (abortOnError . getModuleModTime)
-- getDepTimes [] = return []
-- getDepTimes (file:files) = catch
--   (do time  <- getModuleModTime file
--       times <- getDepTimes files
--       return (time:times))
--   (\err -> abortWith [show err])

--
outOfDate :: [ClockTime] -> [ClockTime] -> Bool
outOfDate tgtimes dptimes = or [ tg < dp | tg <- tgtimes, dp <- dptimes]
-- outOfDate tgtimes dptimes = or (map (\t -> or (map ((<) t) dptimes)) tgtimes)
