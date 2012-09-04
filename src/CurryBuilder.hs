{- |
    Module      :  $Header$
    Description :  Build tool for compiling multiple Curry modules
    Copyright   :  (c) 2005, Martin Engelke    (men@informatik.uni-kiel.de)
                       2007, Sebastian Fischer (sebf@informatik.uni-kiel.de)
                       2011, Björn Peemöller   (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains functions to generate Curry representations for a
    Curry source file including all imported modules.
-}
module CurryBuilder (buildCurry, smake) where

import Control.Monad   (liftM)
import Data.Maybe      (catMaybes, mapMaybe)
import System.FilePath (normalise)
import System.Time     (ClockTime)

import Curry.Base.Ident
import Curry.Files.Filenames
import Curry.Files.PathUtils

import Base.Messages (info, status, abortWith)

import CompilerOpts (Options (..), TargetType (..))
import CurryDeps    (Source (..), flatDeps)
import Modules      (compileModule)

-- |Compile the Curry module in the given source file including all imported
-- modules, depending on the 'Options'.
buildCurry :: Options -> String -> IO ()
buildCurry opts s = do
  target <- findCurry opts s
  case target of
    Left err -> abortWith [err]
    Right fn -> do
      (srcs, depErrs) <- flatDeps opts fn
      if not $ null depErrs
        then abortWith depErrs
        else makeCurry (defaultToFlatCurry opts) srcs fn
      where
      defaultToFlatCurry opt
        | null $ optTargetTypes opt = opt { optTargetTypes = [FlatCurry] }
        | otherwise                 = opt

-- |Search for a compilation target identified by the given 'String'.
findCurry :: Options -> String -> IO (Either String FilePath)
findCurry opts s = do
  mbTarget <- findFile `orIfNotFound` findModule
  case mbTarget of
    Nothing -> return $ Left  complaint
    Just fn -> return $ Right fn
  where
  canBeFile    = isCurryFilePath s
  canBeModule  = isValidModuleName s
  moduleFile   = moduleNameToFile $ fromModuleName s
  paths        = optImportPaths opts
  findFile     = if canBeFile
                    then lookupCurryFile paths s
                    else return Nothing
  findModule   = if canBeModule
                    then lookupCurryFile paths moduleFile
                    else return Nothing
  complaint
    | canBeFile && canBeModule = errMissingTarget s
    | canBeFile                = errMissingFile   s
    | canBeModule              = errMissingModule s
    | otherwise                = errUnrecognized  s
  first `orIfNotFound` second = do
    mbFile <- first
    case mbFile of
      Nothing -> second
      justFn  -> return justFn

-- |Compiles the given source modules, which must be in topological order
makeCurry :: Options -> [(ModuleIdent, Source)] -> FilePath -> IO ()
makeCurry opts srcs targetFile = mapM_ (process . snd) srcs
  where
  process (Source fn deps) = do
    let isFinalFile = dropExtension targetFile == dropExtension fn
        isEnforced  = optForce opts || (not $ null $ optDumps opts)

        destFiles   = if isFinalFile then destNames fn else [getFlatName fn]
        depFiles    = fn : mapMaybe flatInterface deps

        actOutdated = if isFinalFile then compileFinal else compile
        actUpToDate = if isFinalFile then skipFinal    else skip

    interfaceExists <- doesModuleExist $ flatIntName fn
    if interfaceExists && not (isEnforced && isFinalFile)
       then smake destFiles depFiles (actOutdated fn) (actUpToDate fn)
       else (actOutdated fn)
  process _ = return ()

  compileFinal f = do
    status opts $ "generating " ++ (normalise $ head $ destNames f)
    compileModule opts f

  compile f = do
    status opts $ "compiling " ++ normalise f
    compileModule (opts { optTargetTypes = [FlatCurry], optDumps = [] }) f

  skipFinal f = status opts $ "skipping " ++ normalise f
  skip      f = info   opts $ "skipping " ++ normalise f

  destNames fn = [ gen fn | (tgt, gen) <- nameGens
                 , tgt `elem` optTargetTypes opts]
    where nameGens =
            [ (FlatCurry            , flatName     )
            , (ExtendedFlatCurry    , extFlatName  )
            , (FlatXml              , xmlName      )
            , (AbstractCurry        , acyName      )
            , (UntypedAbstractCurry , uacyName     )
            , (Parsed               , sourceRepName)
            ]

  flatInterface m = case lookup m srcs of
    Just (Source fn  _) -> Just $ flatIntName fn
    Just (Interface fn) -> Just $ flatIntName fn
    _                   -> Nothing

  getFlatName = if ExtendedFlatCurry `elem` optTargetTypes opts
                   then extFlatName
                   else flatName

-- |A simple make function
smake :: [FilePath] -- ^ destination files
      -> [FilePath] -- ^ dependency files
      -> IO a       -- ^ action to perform if depedency files are newer
      -> IO a       -- ^ action to perform if destination files are newer
      -> IO a
smake dests deps actOutdated actUpToDate = do
  destTimes <- getDestTimes dests
  depTimes  <- getDepTimes deps
  make destTimes depTimes
  where
  make destTimes depTimes
    | length destTimes < length dests = actOutdated
    | outOfDate destTimes depTimes    = actOutdated
    | otherwise                       = actUpToDate

  getDestTimes :: [FilePath] -> IO [ClockTime]
  getDestTimes = liftM catMaybes . mapM getModuleModTime

  getDepTimes :: [FilePath] -> IO [ClockTime]
  getDepTimes = mapM (abortOnMissing getModuleModTime)

  outOfDate :: [ClockTime] -> [ClockTime] -> Bool
  outOfDate tgtimes dptimes = or [ tg < dp | tg <- tgtimes, dp <- dptimes]

  abortOnMissing :: (FilePath -> IO (Maybe a)) -> FilePath -> IO a
  abortOnMissing act f = act f >>= \res -> case res of
    Nothing  -> abortWith [errModificationTime f]
    Just val -> return val

errMissingFile :: String -> String
errMissingFile f = "Missing file " ++ quote f

errMissingModule :: String -> String
errMissingModule f = "Missing module " ++ quote f

errMissingTarget :: String -> String
errMissingTarget f = "Missing target " ++ quote f

errUnrecognized :: String -> String
errUnrecognized f = "Unrecognized input " ++ quote f

errModificationTime :: FilePath -> String
errModificationTime f = "Could not inspect modification time of file "
                        ++ quote f

quote :: String -> String
quote s = "\"" ++ s ++ "\""
