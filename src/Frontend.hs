{- |
    Module      :  $Header$
    Description :  API to access cymake as a library
    Copyright   :  (c) 2005, Martin Engelke (men@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides an API for dealing with several kinds of Curry
    program representations.
-}

-- TODO: Should be updated/refactored

module Frontend (parse, fullParse, typingParse) where

import Data.Maybe (mapMaybe)
import qualified Data.Map as Map (empty)
import Control.Monad.Writer

import Curry.Base.MessageMonad
import Curry.Files.Filenames
import Curry.Files.PathUtils
import Curry.Syntax (Module (..), parseModule)

import Checks
import CompilerEnv
import CompilerOpts (Options (..), Verbosity (..), TargetType (..), defaultOptions)
import CurryBuilder (smake)
import CurryDeps (Source (..), flattenDeps, moduleDeps)
import Imports (importModules)
import Interfaces (loadInterfaces)
import Modules

{- |Return the result of a syntactical analysis of the source program 'src'.
    The result is the syntax tree of the program (type 'Module'; see Module
    "CurrySyntax").
-}
parse :: FilePath -> String -> MsgMonad Module
parse fn src = parseModule True fn src >>= genCurrySyntax fn

{- |Return the syntax tree of the source program 'src' (type 'Module'; see
    Module "CurrySyntax") after resolving the category (i.e. function,
    constructor or variable) of an identifier. 'fullParse' always
    searches for standard Curry libraries in the path defined in the
    environment variable "PAKCSLIBPATH". Additional search paths can
    be defined using the argument 'paths'.
-}
fullParse :: [FilePath] -> FilePath -> String -> IO (MsgMonad Module)
fullParse paths fn src = genFullCurrySyntax checkModule paths fn $ parse fn src

{- |Behaves like 'fullParse', but returns the syntax tree of the source
    program 'src' (type 'Module'; see Module "CurrySyntax") after inferring
    the types of identifiers.
-}
typingParse :: [FilePath] -> FilePath -> String -> IO (MsgMonad Module)
typingParse paths fn src = genFullCurrySyntax checkModule paths fn $ parse fn src

--
genCurrySyntax :: FilePath -> Module -> MsgMonad Module
genCurrySyntax fn mod1
  | null hdrErrs = return mdl
  | otherwise    = failWith $ head hdrErrs
  where (mdl, hdrErrs) = checkModuleHeader defaultOptions fn mod1

--
genFullCurrySyntax ::
  (Options -> CompilerEnv -> Module -> CheckResult (CompilerEnv, Module))
  -> [FilePath] -> FilePath -> MsgMonad Module -> IO (MsgMonad Module)
genFullCurrySyntax check paths fn m = runMsgIO m $ \mod1 -> do
  errs <- makeInterfaces paths fn mod1
  if null errs
    then do
      (iEnv, intfErrs) <- loadInterfaces paths mod1
      unless (null intfErrs) $ failWith $ msgTxt $ head intfErrs
      let env = importModules opts mod1 iEnv
      case check opts env mod1 of
        CheckSuccess (_, mod') -> return (return  mod')
        CheckFailed errs'      -> return $ failWith $ msgTxt $ head errs'
    else return $ failWith $ head errs
  where opts = mkOpts paths

-- TODO: Resembles CurryBuilder

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces ::  [FilePath] -> FilePath -> Module -> IO [String]
makeInterfaces paths fn mdl = do
  (deps1, errs) <- fmap flattenDeps $ moduleDeps (mkOpts paths) Map.empty fn mdl
  when (null errs) $ mapM_ (compile deps1 . snd) deps1
  return errs
  where
    compile deps' (Source file' mods) = smake
      [flatName file', flatIntName file']
      (file':mapMaybe (flatInterface deps') mods)
      (compileModule (mkOpts paths) file')
      (return ())
    compile _ _ = return ()

    flatInterface deps' mod1 = case lookup mod1 deps' of
      Just (Source f  _) -> Just $ flatIntName $ dropExtension f
      Just (Interface f) -> Just $ flatIntName $ dropExtension f
      _                  -> Nothing

mkOpts :: [FilePath] -> Options
mkOpts paths = defaultOptions
  { optImportPaths = paths
  , optVerbosity   = VerbQuiet
  , optWarn        = False
  , optTargetTypes = [AbstractCurry]
  }
