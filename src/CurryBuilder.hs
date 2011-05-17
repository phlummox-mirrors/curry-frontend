{- |CurryBuilder - Generates Curry representations for a Curry source file
                   including all imported modules.

    September 2005, Martin Engelke (men@informatik.uni-kiel.de)
    March 2007, extensions by Sebastian Fischer (sebf@informatik.uni-kiel.de)
    May 2011, refinements b Bjoern Peemoeller  (bjp@informatik.uni-kiel.de)
-}
module CurryBuilder (buildCurry, smake) where

import Control.Monad (liftM, unless)
import Data.Maybe (catMaybes, fromMaybe)
import System.Time (ClockTime)

import Curry.Base.Ident
import Curry.Files.Filenames
import Curry.Files.PathUtils ( dropExtension, doesModuleExist, getCurryPath
  , getModuleModTime, tryGetModuleModTime)

import CompilerOpts (Options (..), Extension (..), TargetType (..))
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
      makeCurry (defaultToFlatCurry opts) deps f
  where
    paths = optImportPaths opts
    implicitPrelude = NoImplicitPrelude `notElem` optExtensions opts
    missingModule f = "Error: missing module \"" ++ f ++ "\""
    defaultToFlatCurry opt
      | null $ optTargetTypes opt = opt { optTargetTypes = [FlatCurry] }
      | otherwise                 = opt

makeCurry :: Options -> [(ModuleIdent, Source)] -> FilePath -> IO ()
makeCurry opts deps1 targetFile = mapM_ (compile . snd) deps1 where

  compile (Interface _) = return ()
  compile Unknown       = return ()
  compile (Source file mods)
      -- target file
    | dropExtension targetFile == dropExtension file = do
        flatIntfExists <- doesModuleExist (flatIntName file)
        if flatIntfExists && not (optForce opts) && null (optDumps opts)
          then smake (targetNames file)
                      (targetFile: (catMaybes (map flatInterface mods)))
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
    | FlatCurry            `elem` optTargetTypes opts = [flatName' opts fn] -- , flatIntName fn]
    | FlatXml              `elem` optTargetTypes opts = [xmlName        fn]
    | AbstractCurry        `elem` optTargetTypes opts = [acyName        fn]
    | UntypedAbstractCurry `elem` optTargetTypes opts = [uacyName       fn]
    | Parsed               `elem` optTargetTypes opts
      = [fromMaybe (sourceRepName fn) (optOutput opts)]
    | otherwise            = [flatName' opts fn] -- , flatIntName fn]

  flatInterface mod1 = case (lookup mod1 deps1) of
    Just (Source file _)  -> Just $ flatIntName file
    Just (Interface file) -> Just $ flatIntName file
    _                     -> Nothing

  compOpts isImport
    | isImport  = opts { optTargetTypes = [FlatCurry], optDumps = [] }
    | otherwise = opts

flatName' :: Options -> FilePath -> FilePath
flatName' opts
  | ExtendedFlatCurry `elem` optTargetTypes opts  = extFlatName
  | otherwise                                     = flatName

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

--
getDestTimes :: [FilePath] -> IO [ClockTime]
getDestTimes = liftM catMaybes . mapM tryGetModuleModTime

--
getDepTimes :: [String] -> IO [ClockTime]
getDepTimes = mapM (abortOnError . getModuleModTime)

--
outOfDate :: [ClockTime] -> [ClockTime] -> Bool
outOfDate tgtimes dptimes = or [ tg < dp | tg <- tgtimes, dp <- dptimes]


abortOnError :: IO a -> IO a
abortOnError act = catch act (\err -> abortWith [show err])
