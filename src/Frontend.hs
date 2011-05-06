{- |Frontend - Provides an API for dealing with several kinds of Curry
    program representations

    December 2005, Martin Engelke (men@informatik.uni-kiel.de)
-}
module Frontend (parse, fullParse, typingParse) where

import Data.Maybe (mapMaybe)
import qualified Data.Map as Map (empty)
import Control.Monad.Writer
import Prelude hiding (lex)

import Curry.Base.MessageMonad
import Curry.Base.Ident
import Curry.Files.Filenames
import Curry.Files.PathUtils
import qualified Curry.Syntax as CS (Module (..), Decl (..), parseModule)

import Modules (checkModule, simpleCheckModule, compileModule, importPrelude
  , patchModuleId, loadInterfaces)
import CurryBuilder (smake)
import CurryCompilerOpts (Options (..), defaultOptions)
import CurryDeps (flattenDeps, moduleDeps, Source (..))
import Base (ModuleEnv)

{- |Return the result of a syntactical analysis of the source program 'src'.
    The result is the syntax tree of the program (type 'Module'; see Module
    "CurrySyntax").
-}
parse :: FilePath -> String -> MsgMonad CS.Module
parse fn src = CS.parseModule True fn src >>= genCurrySyntax fn

{- |Return the syntax tree of the source program 'src' (type 'Module'; see
    Module "CurrySyntax") after resolving the category (i.e. function,
    constructor or variable) of an identifier. 'fullParse' always
    searches for standard Curry libraries in the path defined in the
    environment variable "PAKCSLIBPATH". Additional search paths can
    be defined using the argument 'paths'.
-}
fullParse :: [FilePath] -> FilePath -> String -> IO (MsgMonad CS.Module)
fullParse paths fn src =
  genFullCurrySyntax simpleCheckModule paths $ parse fn src

{- |Behaves like 'fullParse', but returns the syntax tree of the source
    program 'src' (type 'Module'; see Module "CurrySyntax") after inferring
    the types of identifiers.
-}
typingParse :: [FilePath] -> FilePath -> String -> IO (MsgMonad CS.Module)
typingParse paths fn src = genFullCurrySyntax checkModule paths $ parse fn src

--
genCurrySyntax :: FilePath -> CS.Module -> MsgMonad (CS.Module)
genCurrySyntax fn mod1
  | isValidModuleId fn mid = return mod'
  | otherwise              = failWith $ err_invalidModuleName mid
  where
  mod'@(CS.Module mid _ _) = patchModuleId fn (importPrelude fn mod1)

  err_invalidModuleName :: ModuleIdent -> String
  err_invalidModuleName m = "module \"" ++ moduleName m
    ++ "\" must be in a file \"" ++ moduleName m ++ ".curry\""

  -- Return 'True', if file name and module name are equal.
  isValidModuleId :: FilePath -> ModuleIdent -> Bool
  isValidModuleId f m = last (moduleQualifiers m) == takeBaseName f

--
genFullCurrySyntax ::
  (Options -> Base.ModuleEnv -> CS.Module -> IO (a, b, c, CS.Module, d, [WarnMsg]))
  -> [FilePath] -> MsgMonad CS.Module -> IO (MsgMonad CS.Module)
genFullCurrySyntax check paths m = runMsgIO m $ \mod1 -> do
  errs <- makeInterfaces paths mod1
  if null errs
    then do
      mEnv <- loadInterfaces paths mod1
      (_, _, _, mod', _, msgs') <- check (opts paths) mEnv mod1
      return (tell msgs' >> return  mod')
    else return (failWith (head errs))

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces ::  [FilePath] -> CS.Module -> IO [String]
makeInterfaces paths (CS.Module mid _ decls) = do
  let imports = [preludeMIdent | mid /= preludeMIdent]
              ++ [imp | CS.ImportDecl _ imp _ _ _ <- decls]
  (deps1, errs) <- fmap flattenDeps (foldM (moduleDeps True paths []) Map.empty imports)
  when (null errs) (mapM_ (compile deps1 . snd) deps1)
  return errs
  where
    compile deps' (Source file' mods) = do
      _ <- smake [flatName file', flatIntName file']
                 (file':mapMaybe (flatInterface deps') mods)
                 (compileModule (opts paths) file')
                 (return Nothing)
      return ()
    compile _ _ = return ()

    flatInterface deps' mod1 = case (lookup mod1 deps') of
      Just (Source file' _)  -> Just (flatIntName (dropExtension file'))
      Just (Interface file') -> Just (flatIntName (dropExtension file'))
      _                      -> Nothing

opts :: [FilePath] -> Options
opts paths = defaultOptions
  { importPaths = paths
  , noVerb      = True
  , noWarn      = True
  , abstract    = True
  }
