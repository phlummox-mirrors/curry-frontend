{- |
    Module      :  $Header$
    Description :  Compilation of a single module
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2015 Björn Peemöller
                       2016        Jan Tikovsky
                       2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module controls the compilation of modules.
-}

module Modules
  ( compileModule, loadAndCheckModule, loadModule, checkModule
  , parseModule, checkModuleHeader
  ) where

import qualified Control.Exception as C   (catch, IOException)
import           Control.Monad            (liftM, unless, when)
import           Data.Char                (toUpper)
import qualified Data.Map          as Map (elems, lookup)
import           Data.Maybe               (fromMaybe)
import           System.Directory         (getTemporaryDirectory, removeFile)
import           System.Exit              (ExitCode (..))
import           System.FilePath          (normalise)
import           System.IO
   (IOMode (ReadMode), Handle, hClose, hGetContents, hPutStr, openFile
  , openTempFile)
import           System.Process           (system)

import Curry.Base.Ident
import Curry.Base.Monad
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.ExtendedFlat.InterfaceEquivalence (eqInterface)
import Curry.Files.Filenames
import Curry.Files.PathUtils
import Curry.Syntax.InterfaceEquivalence

import Base.Messages
import Env.Interface

-- source representations
import qualified Curry.AbstractCurry as AC
import qualified Curry.ExtendedFlat  as EF
import qualified Curry.Syntax        as CS
import qualified IL                  as IL

import Checks
import CompilerEnv
import CompilerOpts
import Exports
import Generators
import Imports
import Interfaces (loadInterfaces)
import ModuleSummary
import Transformations

-- The function 'compileModule' is the main entry-point of this
-- module for compiling a Curry source module. Depending on the command
-- line options, it will emit either FlatCurry code or AbstractCurry code
-- (typed, untyped or with type signatures) for the module.
-- Usually, the first step is to check the module.
-- Then the code is translated into the intermediate
-- language. If necessary, this phase will also update the module's
-- interface file. The resulting code then is written out
-- to the corresponding file.
-- The untyped  AbstractCurry representation is written
-- out directly after parsing and simple checking the source file.
-- The typed AbstractCurry code is written out after checking the module.
--
-- The compiler automatically loads the prelude when compiling any
-- module, except for the prelude itself, by adding an appropriate import
-- declaration to the module.
compileModule :: Options -> FilePath -> CYIO ()
compileModule opts fn = do
  (env, mdl) <- loadAndCheckModule opts fn
  liftIO $ writeOutput opts fn (env, mdl)

loadAndCheckModule :: Options -> FilePath -> CYIO (CompEnv CS.Module)
loadAndCheckModule opts fn = do
  (env, mdl) <- loadModule opts fn >>= checkModule opts
  warn (optWarnOpts opts) $ warnCheck opts env mdl
  return (env, mdl)

-- ---------------------------------------------------------------------------
-- Loading a module
-- ---------------------------------------------------------------------------

loadModule :: Options -> FilePath -> CYIO (CompEnv CS.Module)
loadModule opts fn = do
  parsed <- parseModule opts fn
  -- check module header
  mdl    <- checkModuleHeader opts fn parsed
  -- load the imported interfaces into an InterfaceEnv
  let paths = map (addCurrySubdir (optUseSubdir opts))
                  ("." : optImportPaths opts)
  iEnv   <- loadInterfaces paths mdl
  checkInterfaces opts iEnv
  is     <- importSyntaxCheck iEnv mdl
  -- add information of imported modules
  cEnv   <- importModules mdl iEnv is
  return (cEnv, mdl)

parseModule :: Options -> FilePath -> CYIO CS.Module
parseModule opts fn = do
  mbSrc <- liftIO $ readModule fn
  case mbSrc of
    Nothing  -> failMessages [message $ text $ "Missing file: " ++ fn]
    Just src -> do
      ul    <- liftCYM $ CS.unlit fn src
      prepd <- preprocess (optPrepOpts opts) fn ul
      liftCYM $ CS.parseModule fn prepd

preprocess :: PrepOpts -> FilePath -> String -> CYIO String
preprocess opts fn src
  | not (ppPreprocess opts) = return src
  | otherwise               = do
    res <- liftIO $ withTempFile $ \ inFn inHdl -> do
      hPutStr inHdl src
      hClose inHdl
      withTempFile $ \ outFn outHdl -> do
        hClose outHdl
        ec <- system $ unwords $
          [ppCmd opts, normalise fn, inFn, outFn] ++ ppOpts opts
        case ec of
          ExitFailure x -> return $ Left [message $ text $
              "Preprocessor exited with exit code " ++ show x]
          ExitSuccess   -> Right `liftM` readFile outFn
    either failMessages ok res

withTempFile :: (FilePath -> Handle -> IO a) -> IO a
withTempFile act = do
  tmp       <- getTemporaryDirectory
  (fn, hdl) <- openTempFile tmp "cymake.curry"
  res       <- act fn hdl
  hClose hdl
  removeFile fn
  return res

checkModuleHeader :: Monad m => Options -> FilePath -> CS.Module
                  -> CYT m CS.Module
checkModuleHeader opts fn = checkModuleId fn
                          . importPrelude opts
                          . CS.patchModuleId fn

-- |Check whether the 'ModuleIdent' and the 'FilePath' fit together
checkModuleId :: Monad m => FilePath -> CS.Module
              -> CYT m CS.Module
checkModuleId fn m@(CS.Module _ mid _ _ _)
  | last (midQualifiers mid) == takeBaseName fn
  = ok m
  | otherwise
  = failMessages [errModuleFileMismatch mid]

-- An implicit import of the prelude is added to the declarations of
-- every module, except for the prelude itself, or when the import is disabled
-- by a compiler option. If no explicit import for the prelude is present,
-- the prelude is imported unqualified, otherwise a qualified import is added.

importPrelude :: Options -> CS.Module -> CS.Module
importPrelude opts m@(CS.Module ps mid es is ds)
    -- the Prelude itself
  | mid == preludeMIdent          = m
    -- disabled by compiler option
  | noImpPrelude                  = m
    -- already imported
  | preludeMIdent `elem` imported = m
    -- let's add it!
  | otherwise                     = CS.Module ps mid es (preludeImp : is) ds
  where
  noImpPrelude = NoImplicitPrelude `elem` optExtensions opts
                 || m `CS.hasLanguageExtension` NoImplicitPrelude
  preludeImp   = CS.ImportDecl NoPos preludeMIdent
                  False   -- qualified?
                  Nothing -- no alias
                  Nothing -- no selection of types, functions, etc.
  imported     = [imp | (CS.ImportDecl _ imp _ _ _) <- is]

checkInterfaces :: Monad m => Options -> InterfaceEnv -> CYT m ()
checkInterfaces opts iEnv = mapM_ checkInterface (Map.elems iEnv)
  where
  checkInterface intf = do
    let env = importInterfaces intf iEnv
    interfaceCheck opts (env, intf)

importSyntaxCheck :: Monad m => InterfaceEnv -> CS.Module -> CYT m [CS.ImportDecl]
importSyntaxCheck iEnv (CS.Module _ _ _ imps _) = mapM checkImportDecl imps
  where
  checkImportDecl (CS.ImportDecl p m q asM is) = case Map.lookup m iEnv of
    Just intf -> CS.ImportDecl p m q asM `liftM` importCheck intf is
    Nothing   -> internalError $ "Modules.importModules: no interface for "
                                    ++ show m

-- ---------------------------------------------------------------------------
-- Checking a module
-- ---------------------------------------------------------------------------

-- TODO: The order of the checks should be improved!
checkModule :: Options -> CompEnv CS.Module -> CYIO (CompEnv CS.Module)
checkModule opts mdl = do
  _   <- dumpCS DumpParsed mdl
  exc <- extensionCheck  opts mdl >>= dumpCS DumpExtensionChecked
  tsc <- typeSyntaxCheck opts exc >>= dumpCS DumpTypeSyntaxChecked
  kc  <- kindCheck       opts tsc >>= dumpCS DumpKindChecked
  sc  <- syntaxCheck     opts kc  >>= dumpCS DumpSyntaxChecked
  pc  <- precCheck       opts sc  >>= dumpCS DumpPrecChecked
  inc <- instanceCheck   opts pc  >>= dumpCS DumpInstanceChecked
  tc  <- typeCheck       opts inc >>= dumpCS DumpTypeChecked
  ec  <- exportCheck     opts tc  >>= dumpCS DumpExportChecked
  return ec
  where dumpCS = dumpWith opts CS.showModule CS.ppModule

-- ---------------------------------------------------------------------------
-- Translating a module
-- ---------------------------------------------------------------------------

transModule :: Options -> CompEnv CS.Module -> IO (CompEnv IL.Module)
transModule opts mdl = do
  desugared   <- dumpCS DumpDesugared     $ desugar      mdl
  simplified  <- dumpCS DumpSimplified    $ simplify     desugared
  lifted      <- dumpCS DumpLifted        $ lift         simplified
  il          <- dumpIL DumpTranslated    $ ilTrans      lifted
  ilCaseComp  <- dumpIL DumpCaseCompleted $ completeCase il
  return ilCaseComp
  where
  dumpCS = dumpWith opts CS.showModule CS.ppModule
  dumpIL = dumpWith opts IL.showModule IL.ppModule

-- ---------------------------------------------------------------------------
-- Writing output
-- ---------------------------------------------------------------------------

writeOutput :: Options -> FilePath -> CompEnv CS.Module -> IO ()
writeOutput opts fn mdl@(_, modul) = do
  writeParsed opts fn modul
  mdl' <- expandExports opts mdl
  qmdl <- dumpWith opts CS.showModule CS.ppModule DumpQualified $ qual mdl'
  writeAbstractCurry opts fn qmdl
  -- generate interface file
  let intf = uncurry exportInterface qmdl
  writeInterface opts fn intf
  when withFlat $ do
    (env2, il) <- transModule opts qmdl
    -- generate target code
    let modSum = summarizeModule (tyConsEnv env2) intf (snd qmdl)
    writeFlat opts fn env2 modSum il
  where
  withFlat = any (`elem` optTargetTypes opts) [FlatCurry, ExtendedFlatCurry]

-- The functions \texttt{genFlat} and \texttt{genAbstract} generate
-- flat and abstract curry representations depending on the specified option.
-- If the interface of a modified Curry module did not change, the
-- corresponding file name will be returned within the result of 'genFlat'
-- (depending on the compiler flag "force") and other modules importing this
-- module won't be dependent on it any longer.

-- |Output the parsed 'Module' on request
writeParsed :: Options -> FilePath -> CS.Module -> IO ()
writeParsed opts fn modul@(CS.Module _ m _ _ _) = when srcTarget $
  writeModule (useSubDir $ sourceRepName fn) source
  where
  srcTarget  = Parsed `elem` optTargetTypes opts
  useSubDir  = addCurrySubdirModule (optUseSubdir opts) m
  source     = CS.showModule modul

writeInterface :: Options -> FilePath -> CS.Interface -> IO ()
writeInterface opts fn intf@(CS.Interface m _ _)
  | optForce opts = outputInterface
  | otherwise     = do
      equal <- C.catch (matchInterface interfaceFile intf) ignoreIOException
      unless equal outputInterface
  where
  ignoreIOException :: C.IOException -> IO Bool
  ignoreIOException _ = return False

  interfaceFile   = interfName fn
  outputInterface = writeModule
                    (addCurrySubdirModule (optUseSubdir opts) m interfaceFile)
                    (show $ CS.ppInterface intf)

matchInterface :: FilePath -> CS.Interface -> IO Bool
matchInterface ifn i = do
  hdl <- openFile ifn ReadMode
  src <- hGetContents hdl
  case runCYM (CS.parseInterface ifn src) of
    Left  _  -> hClose hdl >> return False
    Right i' -> return (i `intfEquiv` fixInterface i')

writeFlat :: Options -> FilePath -> CompilerEnv -> ModuleSummary -> IL.Module
          -> IO ()
writeFlat opts fn env modSum il = do
  when (extTarget || fcyTarget) $ do
    writeFlatCurry opts fn env modSum il
    writeFlatIntf  opts fn env modSum il
  where
  extTarget = ExtendedFlatCurry `elem` optTargetTypes opts
  fcyTarget = FlatCurry         `elem` optTargetTypes opts

-- |Export an 'IL.Module' into a FlatCurry file
writeFlatCurry :: Options -> FilePath -> CompilerEnv -> ModuleSummary
               -> IL.Module -> IO ()
writeFlatCurry opts fn env modSum il = do
  (_, fc) <- dumpWith opts show EF.ppProg DumpFlatCurry (env, prog)
  when extTarget $ EF.writeExtendedFlat (useSubDir $ extFlatName fn) fc
  when fcyTarget $ EF.writeFlatCurry    (useSubDir $ flatName    fn) fc
  where
  extTarget = ExtendedFlatCurry `elem` optTargetTypes opts
  fcyTarget = FlatCurry         `elem` optTargetTypes opts
  useSubDir = addCurrySubdirModule (optUseSubdir opts) (moduleIdent env)
  prog      = genFlatCurry modSum env il

writeFlatIntf :: Options -> FilePath -> CompilerEnv -> ModuleSummary
              -> IL.Module -> IO ()
writeFlatIntf opts fn env modSum il
  | not (optInterface opts) = return ()
  | optForce opts           = outputInterface
  | otherwise               = do
      mfint <- EF.readFlatInterface targetFile
      let oldInterface = fromMaybe emptyIntf mfint
      when (mfint == mfint) $ return () -- necessary to close file -- TODO
      unless (oldInterface `eqInterface` intf) $ outputInterface
  where
  targetFile      = flatIntName fn
  emptyIntf       = EF.Prog "" [] [] [] []
  intf            = genFlatInterface modSum env il
  useSubDir       = addCurrySubdirModule (optUseSubdir opts) (moduleIdent env)
  outputInterface = EF.writeFlatCurry (useSubDir targetFile) intf

writeAbstractCurry :: Options -> FilePath -> CompEnv CS.Module -> IO ()
writeAbstractCurry opts fname (env, modul) = do
  when acyTarget  $ AC.writeCurry (useSubDir $ acyName fname)
                  $ genTypedAbstractCurry env modul
  when uacyTarget $ AC.writeCurry (useSubDir $ uacyName fname)
                  $ genUntypedAbstractCurry env modul
  where
  acyTarget  = AbstractCurry        `elem` optTargetTypes opts
  uacyTarget = UntypedAbstractCurry `elem` optTargetTypes opts
  useSubDir  = addCurrySubdirModule (optUseSubdir opts) (moduleIdent env)

type Dump = (DumpLevel, CompilerEnv, String)

dumpWith :: (MonadIO m, Show a)
         => Options -> (a -> String) -> (a -> Doc) -> DumpLevel
         -> CompEnv a -> m (CompEnv a)
dumpWith opts rawView view lvl res@(env, mdl) = do
  let str = if dbDumpRaw (optDebugOpts opts) then rawView mdl
                                             else show (view mdl)
  doDump (optDebugOpts opts) (lvl, env, str)
  return res

-- |Translate FlatCurry into the intermediate language 'IL'
-- |The 'dump' function writes the selected information to standard output.
doDump :: MonadIO m => DebugOpts -> Dump -> m ()
doDump opts (level, env, dump)
  = when (level `elem` dbDumpLevels opts) $ liftIO $ do
      putStrLn (heading (capitalize $ lookupHeader dumpLevel) '=')
      when (dbDumpEnv opts) $ do
        putStrLn (heading "Environment" '-')
        putStrLn (showCompilerEnv env)
      putStrLn (heading "Source Code" '-')
      putStrLn dump
  where
  heading h s = '\n' : h ++ '\n' : replicate (length h) s
  lookupHeader []            = "Unknown dump level " ++ show level
  lookupHeader ((l,_,h):lhs)
    | level == l = h
    | otherwise  = lookupHeader lhs
  capitalize = unwords . map firstUpper . words
  firstUpper ""     = ""
  firstUpper (c:cs) = toUpper c : cs

errModuleFileMismatch :: ModuleIdent -> Message
errModuleFileMismatch mid = posMessage mid $ hsep $ map text
  [ "Module", moduleName mid, "must be in a file"
  , moduleName mid ++ ".(l)curry" ]
