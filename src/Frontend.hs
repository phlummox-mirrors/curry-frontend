{- |Frontend - Provides an API for dealing with several kinds of Curry
    program representations

    December 2005, Martin Engelke (men@informatik.uni-kiel.de)
-}
module Frontend (parse, fullParse, typingParse) where

import Data.Maybe (mapMaybe)
import qualified Data.Map as Map (empty)
import Control.Monad.Writer

import Curry.Base.MessageMonad
import Curry.Files.Filenames
import Curry.Files.PathUtils
import Curry.Syntax (Module (..), Interface, parseModule)

import Env.Interfaces

import CompilerEnv
import CompilerOpts (Options (..), Verbosity (..), TargetType (..), defaultOptions)
import CurryBuilder (smake)
import CurryDeps (Source (..), flattenDeps, moduleDeps)
import Interfaces (loadInterfaces)
import Modules (checkModuleHeader, checkModule, simpleCheckModule, compileModule)

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
fullParse paths fn src =
  genFullCurrySyntax simpleCheckModule paths fn $ parse fn src

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
  (Options -> InterfaceEnv -> Module -> (CompilerEnv, Module, Interface, [Message]))
  -> [FilePath] -> FilePath -> MsgMonad Module -> IO (MsgMonad Module)
genFullCurrySyntax check paths fn m = runMsgIO m $ \mod1 -> do
  errs <- makeInterfaces paths fn mod1
  if null errs
    then do
      iEnv <- loadInterfaces paths mod1
      let (_, mod', _, msgs') = check (opts paths) iEnv mod1
      return (tell msgs' >> return  mod')
    else return $ failWith $ head errs

-- TODO: Resembles CurryBuilder

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces ::  [FilePath] -> FilePath -> Module -> IO [String]
makeInterfaces paths fn mdl = do
  (deps1, errs) <- fmap flattenDeps $ moduleDeps defaultOptions paths Map.empty fn mdl
  when (null errs) $ mapM_ (compile deps1 . snd) deps1
  return errs
  where
    compile deps' (Source file' mods) = smake
      [flatName file', flatIntName file']
      (file':mapMaybe (flatInterface deps') mods)
      (compileModule (opts paths) file')
      (return ())
    compile _ _ = return ()

    flatInterface deps' mod1 = case lookup mod1 deps' of
      Just (Source f  _) -> Just $ flatIntName $ dropExtension f
      Just (Interface f) -> Just $ flatIntName $ dropExtension f
      _                  -> Nothing

opts :: [FilePath] -> Options
opts paths = defaultOptions
  { optImportPaths = paths
  , optVerbosity   = Quiet
  , optWarn        = False
  , optTargetTypes = [AbstractCurry]
  }
