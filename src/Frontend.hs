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
module Frontend (parse, fullParse) where

import           Control.Monad.Writer
import           Data.Maybe           (mapMaybe)
import qualified Data.Map as Map      (empty)


import Curry.Base.Message
import Curry.Files.Filenames
import Curry.Files.PathUtils
import Curry.Syntax (Module (..), parseModule)

import Checks       (CheckResult (..))
import CompilerOpts (Options (..), defaultOptions)
import CurryBuilder (smake)
import CurryDeps    (Source (..), flattenDeps, moduleDeps)
import Modules      (checkModule, checkModuleHeader, compileModule, loadModule)

{- |Return the result of a syntactical analysis of the source program 'src'.
    The result is the syntax tree of the program (type 'Module'; see Module
    "CurrySyntax").
-}
parse :: FilePath -> String -> MessageM Module
parse fn src = parseModule True fn src >>= genCurrySyntax
  where
  genCurrySyntax mod1
    | null hdrErrs = return mdl
    | otherwise    = failWith $ show $ head hdrErrs
    where (mdl, hdrErrs) = checkModuleHeader defaultOptions fn mod1

{- |Return the syntax tree of the source program 'src' (type 'Module'; see
    Module "CurrySyntax").after inferring the types of identifiers.
    'fullParse' always searches for standard Curry libraries in the path
    defined in the
    environment variable "PAKCSLIBPATH". Additional search paths can
    be defined using the argument 'paths'.
-}
fullParse :: Options -> FilePath -> String -> MessageIO Module
fullParse opts fn src = genFullCurrySyntax opts fn $ parse fn src

genFullCurrySyntax :: Options -> FilePath -> MessageM Module -> MessageIO Module
genFullCurrySyntax opts fn m = case runMsg m of
  Left err        -> failWith $ show err
  Right (mod1, _) -> do
  errs <- liftIO $ makeInterfaces opts fn mod1
  if null errs
    then do
      loaded <- liftIO $ loadModule opts fn
      case checkModule opts loaded of
        CheckFailed errs'        -> failWith $ show $ head errs'
        CheckSuccess (_, mod',_) -> return  mod'
    else failWith $ show $ head errs

-- TODO: Resembles CurryBuilder

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces :: Options -> FilePath -> Module -> IO [Message]
makeInterfaces opts fn mdl = do
  (deps1, errs) <- fmap flattenDeps $ moduleDeps opts Map.empty fn mdl
  when (null errs) $ mapM_ (compile deps1 . snd) deps1
  return errs
  where
    compile deps' (Source file' mods) = smake
      [flatName file', flatIntName file']
      (file':mapMaybe (flatInterface deps') mods)
      (compileModule opts file')
      (return ())
    compile _ _ = return ()

    flatInterface deps' mod1 = case lookup mod1 deps' of
      Just (Source f  _) -> Just $ flatIntName $ dropExtension f
      Just (Interface f) -> Just $ flatIntName $ dropExtension f
      _                  -> Nothing
