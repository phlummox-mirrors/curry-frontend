{- |
    Module      :  $Header$
    Description :  Build tool for compiling multiple Curry modules
    Copyright   :  (c) 2005, Martin Engelke (men@informatik.uni-kiel.de)
                       2007, Sebastian Fischer (sebf@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains functions to generate Curry representations for a
    Curry source file including all imported modules.
-}
module CurryBuilder (buildCurry, smake) where

import qualified Control.Exception as C (SomeException (..), catch)
import Control.Monad (liftM)
import Data.Maybe (catMaybes, mapMaybe)
import System.Time (ClockTime)

import Curry.Base.Ident
import Curry.Files.Filenames
import Curry.Files.PathUtils

import Base.Messages (info, status, abortWith)

import CompilerOpts (Options (..), TargetType (..))
import CurryDeps (Source (..), flatDeps)
import Modules (compileModule)

-- |Compile the Curry module in the given source file including all imported
-- modules, depending on the 'Options'.
buildCurry :: Options -> String -> IO ()
buildCurry opts str = do
  target <- findCurry opts str
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

findCurry :: Options -> String -> IO (Either String FilePath)
findCurry opts str = do
  mbTarget <- fileSearch `orIfNotFound` moduleSearch
  case mbTarget of
    Nothing -> return $ Left  complaint
    Just fn -> return $ Right fn
  where
  canBeFile    = isCurryFilePath str
  canBeModule  = isModuleName    str
  moduleFile   = moduleNameToFile $ fromModuleName str
  paths        = optImportPaths opts
  fileSearch   = if canBeFile
                    then lookupCurryFile paths str
                    else return Nothing
  moduleSearch = if canBeModule
                    then lookupCurryFile paths moduleFile
                    else return Nothing
  complaint
    | canBeFile && canBeModule = errMissingTarget str
    | canBeFile                = errMissingFile   str
    | canBeModule              = errMissingModule str
    | otherwise                = errUnrecognized  str
  first `orIfNotFound` second = do
    mbFile <- first
    case mbFile of
      Nothing -> second
      justFn  -> return justFn

-- |Compiles the given source modules, which must be in topological order
makeCurry :: Options -> [(ModuleIdent, Source)] -> FilePath -> IO ()
makeCurry opts srcs targetFile = mapM_ (compile . snd) srcs where
  compile (Source fn deps) = do
    interfaceExists <- doesModuleExist $ flatIntName fn

    let isFinalFile = dropExtension targetFile == dropExtension fn
        isEnforced  = optForce opts || (not $ null $ optDumps opts)
        destFiles   = if isFinalFile then destNames fn else [flatName' fn]
        depFiles    = fn : mapMaybe flatInterface deps
        actOutdated = if isFinalFile then generateFile  fn else compileFile fn
        actUpToDate = if isFinalFile then skipFinalFile fn else skipFile fn

    if interfaceExists && not (isEnforced && isFinalFile)
       then smake destFiles depFiles actOutdated actUpToDate
       else actOutdated
  compile _ = return ()

  compileFile f = do
    status opts $ "compiling " ++ f
    compileModule (opts { optTargetTypes = [FlatCurry], optDumps = [] }) f

  skipFinalFile f = status opts $ "skipping " ++ f

  skipFile f = info opts $ "skipping " ++ f

  generateFile f = do
    status opts $ "generating " ++ head (destNames f)
    compileModule opts f

  destNames fn = [ gen fn | (tgt, gen) <- nameGens
               , tgt `elem` optTargetTypes opts]
    where nameGens =
            [ (FlatCurry            , flatName     )
            , (ExtendedFlatCurry    , extFlatName  )
            , (FlatXml              , xmlName      )
            , (AbstractCurry        , acyName      )
            , (UntypedAbstractCurry , uacyName     )
            , (Parsed               , sourceRepName)
            , (FlatXml              , xmlName      )
            ]

  flatInterface m = case lookup m srcs of
    Just (Source fn  _) -> Just $ flatIntName fn
    Just (Interface fn) -> Just $ flatIntName fn
    _                   -> Nothing

  extTarget = ExtendedFlatCurry `elem` optTargetTypes opts
  flatName' = if extTarget then extFlatName else flatName

-- |A simple make function
smake :: [FilePath] -- ^ destination files
      -> [FilePath] -- ^ dependency files
      -> IO a       -- ^ action to perform if depedency files are newer
      -> IO a       -- ^ action to perform if destination files are newer
      -> IO a
smake dests deps actOutdated actUpToDate = do
  destTimes <- getDestTimes dests
  depTimes  <- getDepTimes deps
  abortOnError $ make destTimes depTimes
  where
    make destTimes depTimes
      | length destTimes < length dests = actOutdated
      | outOfDate destTimes depTimes    = actOutdated
      | otherwise                       = actUpToDate

    getDestTimes :: [FilePath] -> IO [ClockTime]
    getDestTimes = liftM catMaybes . mapM tryGetModuleModTime

    getDepTimes :: [FilePath] -> IO [ClockTime]
    getDepTimes = mapM (abortOnError . getModuleModTime)

    outOfDate :: [ClockTime] -> [ClockTime] -> Bool
    outOfDate tgtimes dptimes = or [ tg < dp | tg <- tgtimes, dp <- dptimes]

    abortOnError :: IO a -> IO a
    abortOnError act = C.catch act handler
      where handler (C.SomeException e) = abortWith [show e]

errMissingFile :: String -> String
errMissingFile f = "Missing file \"" ++ f ++ "\""

errMissingModule :: String -> String
errMissingModule f = "Missing module \"" ++ f ++ "\""

errMissingTarget :: String -> String
errMissingTarget f = "Missing target \"" ++ f ++ "\""

errUnrecognized :: String -> String
errUnrecognized f = "Unrecognized input \"" ++ f ++ "\""