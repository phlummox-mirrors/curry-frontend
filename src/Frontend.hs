{- |
    Module      :  $Header$
    Description :  API to access cymake as a library
    Copyright   :  (c) 2005        Martin Engelke
                       2011 - 2014 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides an API for dealing with several kinds of Curry
    program representations.
-}
module Frontend (parse, fullParse) where

import           Control.Monad.Writer
import           Control.Monad.Trans.Either


import Curry.Base.Message
import Curry.Syntax       (Module (..), parseModule)

import CompilerOpts       (Options (..), defaultOptions)
import CurryBuilder       (buildCurry)
import Modules            (loadAndCheckModule, checkModuleHeader)

{- |Return the result of a syntactical analysis of the source program 'src'.
    The result is the syntax tree of the program (type 'Module'; see Module
    "CurrySyntax").
-}
parse :: FilePath -> String -> MessageM Module
parse fn src = parseModule fn src >>= genCurrySyntax
  where
  genCurrySyntax mod1 = do
    checked <- lift $ runEitherT $ checkModuleHeader defaultOptions fn mod1
    case checked of
      Left hdrErrs -> failWith $ show $ head hdrErrs
      Right mdl    -> return mdl

{- |Return the syntax tree of the source program 'src' (type 'Module'; see
    Module "CurrySyntax").after inferring the types of identifiers.
    'fullParse' always searches for standard Curry libraries in the path
    defined in the
    environment variable "PAKCSLIBPATH". Additional search paths can
    be defined using the argument 'paths'.
-}
fullParse :: Options -> FilePath -> String -> MessageIO Module
fullParse opts fn _ = do
  errs <- liftIO $ makeInterfaces opts fn
  if null errs
    then do
      checked <- liftIO $ runEitherT $ loadAndCheckModule opts fn
      case checked of
        Left errs'      -> failWith $ show $ head errs'
        Right (_, mod') -> return mod'
    else failWith $ show $ head errs

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces :: Options -> FilePath -> IO [Message]
makeInterfaces opts fn = do
  res <- runEitherT $ buildCurry opts fn
  case res of
    Left  errs -> return errs
    Right _    -> return []
