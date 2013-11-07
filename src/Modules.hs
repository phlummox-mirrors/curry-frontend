{- |
    Module      :  $Header$
    Description :  Compilation of a single module
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2013 Björn Peemöller
                       2013        Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module controls the compilation of modules.
-}

module Modules
  ( compileModule, loadModule, checkModuleHeader, checkModule, writeOutput
  ) where

import qualified Control.Exception as C (catch, IOException)
import           Control.Monad   (unless, when)
import qualified Data.Map as Map (elems)
import           Data.Maybe      (fromMaybe)
import           System.IO       (hClose, hGetContents, openFile, IOMode (ReadMode))
import           Text.PrettyPrint
-- import Control.Monad.IO.Class
-- import Control.Monad.Trans.Either

import Curry.Base.Ident
import Curry.Base.Message (runMsg)
import Curry.Base.Position
import Curry.ExtendedFlat.InterfaceEquality (eqInterface)
import Curry.Files.Filenames
import Curry.Files.PathUtils

import Base.Messages
import Env.Interface

-- source representations
import qualified Curry.AbstractCurry as AC
import qualified Curry.ExtendedFlat.Type as EF
import qualified Curry.Syntax as CS
import qualified IL as IL

import Checks
import CompilerEnv
import CompilerOpts
import Exports
import Generators
import Imports
import InterfaceEquivalence
import Interfaces
import ModuleSummary
import Transformations

-- The function 'compileModule' is the main entry-point of this
-- module for compiling a Curry source module. Depending on the command
-- line options, it will emit either FlatCurry code (standard or in XML
-- representation) or AbstractCurry code (typed, untyped or with type
-- signatures) for the module
-- Usually, the first step is to check the module.
-- Then the code is translated into the intermediate
-- language. If necessary, this phase will also update the module's
-- interface file. The resulting code then is written out (in
-- FlatCurry or XML format) to the corresponding file.
-- The untyped  AbstractCurry representation is written
-- out directly after parsing and simple checking the source file.
-- The typed AbstractCurry code is written out after checking the module.
--
-- The compiler automatically loads the prelude when compiling any
-- module, except for the prelude itself, by adding an appropriate import
-- declaration to the module.

compileModule :: Options -> FilePath -> CYIO ()
compileModule opts fn = do
  (env, mdl, tcExportEnv, tcExportMdl) <- loadModule opts fn >>= checkModule opts
  warn opts $ warnCheck opts env mdl
  liftIO $ writeOutput opts fn (env, mdl) (tcExportEnv, tcExportMdl)

-- ---------------------------------------------------------------------------
-- Loading a module
-- ---------------------------------------------------------------------------

loadModule :: Options -> FilePath -> CYIO (CompilerEnv, CompilerEnv, CS.Module)
loadModule opts fn = do
  parsed <- parseModule fn
  -- check module header
  mdl    <- checkModuleHeader opts fn parsed
  -- load the imported interfaces into an InterfaceEnv
  iEnv   <- loadInterfaces False (optImportPaths opts) mdl
  iEnvTc <- loadInterfaces True (optImportPaths opts) mdl
  checkInterfaces opts iEnv >> checkInterfaces opts iEnvTc
  -- add information of imported modules
  env    <- importModules False opts mdl iEnv
  envtc  <- importModules True opts mdl iEnvTc
  return (env, envtc, mdl)

parseModule :: FilePath -> CYIO CS.Module
parseModule fn = do
  mbSrc <- liftIO $ readModule fn
  case mbSrc of
    Nothing  -> left [message $ text $ "Missing file: " ++ fn]
    Just src -> do
      -- parse module
      case runMsg (CS.parseModule fn src) of
        Left  err         -> left [err]
        Right (parsed, _) -> right parsed

checkModuleHeader :: Monad m => Options -> FilePath -> CS.Module
                  -> CYT m CS.Module
checkModuleHeader opts fn = checkModuleId fn
                          . importPrelude opts fn
                          . CS.patchModuleId fn

-- |Check whether the 'ModuleIdent' and the 'FilePath' fit together
checkModuleId :: Monad m => FilePath -> CS.Module
              -> CYT m CS.Module
checkModuleId fn m@(CS.Module mid _ _ _)
  | last (midQualifiers mid) == takeBaseName fn
  = right m
  | otherwise
  = left [errModuleFileMismatch mid]

-- An implicit import of the prelude is added to the declarations of
-- every module, except for the prelude itself, or when the import is disabled
-- by a compiler option. If no explicit import for the prelude is present,
-- the prelude is imported unqualified, otherwise a qualified import is added.

importPrelude :: Options -> FilePath -> CS.Module -> CS.Module
importPrelude opts fn m@(CS.Module mid es is ds)
    -- the Prelude itself
  | mid == preludeMIdent          = m
    -- disabled by compiler option
  | noImpPrelude                  = m
    -- already imported
  | preludeMIdent `elem` imported = m
    -- let's add it!
  | otherwise                     = CS.Module mid es (preludeImp : is) ds
  where
  noImpPrelude = NoImplicitPrelude `elem` optExtensions opts
  preludeImp   = CS.ImportDecl (first fn) preludeMIdent
                  False   -- qualified?
                  Nothing -- no alias
                  Nothing -- no selection of types, functions, etc.
  imported     = [imp | (CS.ImportDecl _ imp _ _ _) <- is]

checkInterfaces :: Monad m => Options -> InterfaceEnv -> CYT m ()
checkInterfaces opts iEnv = mapM_ checkInterface (Map.elems iEnv)
  where
  checkInterface intf = do
    _ <- interfaceCheck opts (importInterfaces opts intf iEnv) intf
    return ()

-- ---------------------------------------------------------------------------
-- Checking a module
-- ---------------------------------------------------------------------------

-- TODO: The order of the checks should be improved!
-- TODO (2012-01-05, bjp): The export specification check for untyped
--   AbstractCurry is deactivated as it requires the value information
--   collected by the type checker.
-- CheckModule returns two export checked modules + the corresponding
-- environments: One still with type class elements, the second without 
-- type class elements. 
checkModule :: Options -> (CompilerEnv, CompilerEnv, CS.Module)
            -> CYIO (CompilerEnv, CS.Module, CompilerEnv, CS.Module)
checkModule opts (envNonTc, envTc, mdl) = do
  doDump opts (DumpParsed       , envTc, show' CS.ppModule mdl)
  (env1,  kc) <- kindCheck opts envTc mdl -- should be only syntax checking ?
  doDump opts (DumpKindChecked  , env1, show' CS.ppModule kc)
  (env2,  sc) <- syntaxCheck opts env1 kc
  doDump opts (DumpSyntaxChecked, env2, show' CS.ppModule sc)
  (env3,  pc) <- precCheck opts env2 sc
  doDump opts (DumpPrecChecked  , env3, show' CS.ppModule pc)
  (env4, tcc) <- typeClassesCheck opts env3 pc
  doDump opts (DumpTypeClassesChecked, env4, show' CS.ppModule tcc)
  (env5,  tc) <- if withTypeCheck
                 then typeCheck False opts env4 tcc
                 else return (env4, tcc)
  doDump opts (DumpTypeChecked  , env5, show' CS.ppModule tc)
  -- Run an export check here for exporting type class specific elements. As
  -- these are compiled out later, we already here have to set aside the
  -- export checked module and the environment 
  (envEc1,   ec1) <- if withTypeCheck 
                     then exportCheck opts env5 tc
                     else return (env5, tc)
  (envEc1', ec1') <- if withTypeCheck
                     then return $ qual opts envEc1 ec1
                     else return (envEc1, ec1)
  -- Continue with the compile process
  (env5b,  dicts) <- if withTypeCheck
                     then insertDicts opts env5 tc
                     else return (env5, tc)
  let (env5c, dicts') = if withTypeCheck
                        then typeSigs env5b dicts
                        else (env5b, dicts)
  doDump opts (DumpDictionaries , env5c, show' CS.ppModule dicts')
  (env5e, tc2) <- if withTypeCheck
                    -- Take the older environment env4 instead of env5c;
                    -- moreover, replace the value/type constructor environments with the 
                    -- value/type constructor environments that contain only *compiled* 
                    -- type class elements (dictionaries, types, selection 
                    -- methods) that are exported from other modules
                    then typeCheck True opts
                           env4 { valueEnv = valueEnv envNonTc, 
                                  tyConsEnv = tyConsEnv envNonTc,
                                  interfaceEnv = interfaceEnv envNonTc } 
                           dicts' 
                    else return (env5c, dicts')
  doDump opts (DumpTypeChecked2 , env5e, show' CS.ppModule tc2)
  (env6,  ec2) <- if withTypeCheck
                  then exportCheck opts env5e tc2
                  else return (env5e, tc2)
  doDump opts (DumpExportChecked, env6, show' CS.ppModule ec2)
  -- (env7,   ql) <- return $ qual opts env6 ec2
  -- doDump opts (DumpQualified    , env7, show' CS.ppModule ql)
  -- return (env7, ql, envEc1', ec1')
  return (env6, ec2, envEc1', ec1')
  where
  withTypeCheck = any (`elem` optTargetTypes opts)
                      [FlatCurry, ExtendedFlatCurry, FlatXml, AbstractCurry]
  show' pp = if optDumpRaw opts then show else show . pp

-- ---------------------------------------------------------------------------
-- Translating a module
-- ---------------------------------------------------------------------------

type Dump = (DumpLevel, CompilerEnv, String)

-- |Translate FlatCurry into the intermediate language 'IL'
transModule :: Options -> CompilerEnv -> CS.Module
            -> (CompilerEnv, IL.Module, [Dump])
transModule opts env mdl = (env5, ilCaseComp, dumps)
  where
  flat' = FlatCurry `elem` optTargetTypes opts
  (desugared , env1) = desugar        mdl        env
  (simplified, env2) = simplify flat' desugared  env1
  (lifted    , env3) = lift           simplified env2
  (il        , env4) = ilTrans  flat' lifted     env3
  (ilCaseComp, env5) = completeCase   il         env4
  dumps = [ (DumpDesugared    , env1, presentCS desugared )
          , (DumpSimplified   , env2, presentCS simplified)
          , (DumpLifted       , env3, presentCS lifted    )
          , (DumpTranslated   , env4, presentIL il        )
          , (DumpCaseCompleted, env5, presentIL ilCaseComp)
          ]
  presentCS = if optDumpRaw opts then show else show . CS.ppModule
  presentIL = if optDumpRaw opts then show else show . IL.ppModule

-- ---------------------------------------------------------------------------
-- Writing output
-- ---------------------------------------------------------------------------

writeOutput :: Options -> FilePath -> (CompilerEnv, CS.Module) 
            -> (CompilerEnv, CS.Module) -> IO ()
writeOutput opts fn (env, modul) (tcExportEnv, tcExportModule) = do
  writeParsed opts fn modul
  let (env1, qlfd) = qual opts env modul
  doDump opts (DumpQualified, env1, show $ CS.ppModule qlfd)
  writeAbstractCurry opts fn env1 qlfd
  when withFlat $ do
    -- checkModule checks types, and then transModule introduces new
    -- functions (by lambda lifting in 'desugar'). Consequence: The
    -- types of the newly introduced functions are not inferred (hsi)
    let (env2, il, dumps) = transModule opts env1 qlfd
    -- dump intermediate results
    mapM_ (doDump opts) dumps
    -- generate interface file
    let intf = exportInterface env2 qlfd False
        tcIntf = exportInterface tcExportEnv tcExportModule True
    writeInterface opts fn [intf, tcIntf]
    -- generate target code
    let modSum = summarizeModule (tyConsEnv env2) intf qlfd
    writeFlat opts fn env2 modSum il
  where
  withFlat = any (`elem` optTargetTypes opts)
              [FlatCurry, FlatXml, ExtendedFlatCurry]

-- The functions \texttt{genFlat} and \texttt{genAbstract} generate
-- flat and abstract curry representations depending on the specified option.
-- If the interface of a modified Curry module did not change, the
-- corresponding file name will be returned within the result of 'genFlat'
-- (depending on the compiler flag "force") and other modules importing this
-- module won't be dependent on it any longer.

-- |Output the parsed 'Module' on request
writeParsed :: Options -> FilePath -> CS.Module -> IO ()
writeParsed opts fn modul = when srcTarget $
  writeModule useSubDir (sourceRepName fn) source
  where
  srcTarget  = Parsed `elem` optTargetTypes opts
  useSubDir  = optUseSubdir opts
  source     = CS.showModule modul

writeInterface :: Options -> FilePath -> [CS.Interface] -> IO ()
writeInterface opts fn [intf, intfTC]
  | optForce opts = outputInterface
  | otherwise     = do
      equal <- C.catch (matchInterface interfaceFile [intf, intfTC]) ignoreIOException
      unless equal outputInterface
  where
  ignoreIOException :: C.IOException -> IO Bool
  ignoreIOException _ = return False

  interfaceFile   = interfName fn
  outputInterface = writeModule (optUseSubdir opts) interfaceFile
                    (show 
                      (CS.ppInterface "interface" intf
                        $$ CS.ppInterface "interfaceTypeClasses" intfTC))
writeInterface _ _ _ = internalError "writeInterfaces"

matchInterface :: FilePath -> [CS.Interface] -> IO Bool
matchInterface ifn [i, itc] = do
  hdl <- openFile ifn ReadMode
  src <- hGetContents hdl
  case runMsg (CS.parseInterface ifn src) of
    Left _        -> hClose hdl >> return False
    Right ([i', itc'], _) -> 
      return (i `intfEquiv` fixInterface i' && itc `intfEquiv` fixInterface itc')
    Right (_, _) -> internalError "matchInterface"
matchInterface _ _ = internalError "matchInterface"

writeFlat :: Options -> FilePath -> CompilerEnv -> ModuleSummary -> IL.Module
          -> IO ()
writeFlat opts fn env modSum il = do
  when (extTarget || fcyTarget) $ do
    writeFlatCurry opts fn env modSum il
    writeFlatIntf  opts fn env modSum il
  when (xmlTarget) $ writeFlatXml opts fn modSum il
  where
  extTarget    = ExtendedFlatCurry `elem` optTargetTypes opts
  fcyTarget    = FlatCurry         `elem` optTargetTypes opts
  xmlTarget    = FlatXml           `elem` optTargetTypes opts

-- |Export an 'IL.Module' into a FlatCurry file
writeFlatCurry :: Options -> FilePath -> CompilerEnv -> ModuleSummary
               -> IL.Module -> IO ()
writeFlatCurry opts fn env modSum il = do
  warn opts msgs
  when extTarget $ EF.writeExtendedFlat useSubDir (extFlatName fn) prog
  when fcyTarget $ EF.writeFlatCurry    useSubDir (flatName    fn) prog
  where
  extTarget    = ExtendedFlatCurry `elem` optTargetTypes opts
  fcyTarget    = FlatCurry         `elem` optTargetTypes opts
  useSubDir    = optUseSubdir opts
  (prog, msgs) = genFlatCurry opts modSum env il

-- |Export an 'IL.Module' into an XML file
writeFlatXml :: Options -> FilePath -> ModuleSummary -> IL.Module -> IO ()
writeFlatXml opts fn modSum il = writeModule useSubDir (xmlName fn) curryXml
  where
  useSubDir = optUseSubdir opts
  curryXml  = shows (IL.xmlModule (interface modSum) (infixDecls modSum) il) "\n"

writeFlatIntf :: Options -> FilePath -> CompilerEnv -> ModuleSummary
              -> IL.Module -> IO ()
writeFlatIntf opts fn env modSum il
  | not (optInterface opts) = return ()
  | optForce opts           = outputInterface
  | otherwise               = do
      mfint <- EF.readFlatInterface targetFile
      let oldInterface = fromMaybe emptyIntf mfint
      when (mfint == mfint) $ return () -- necessary to close file -- TODO
      unless (oldInterface `eqInterface` newInterface) $ outputInterface
  where
  targetFile = flatIntName fn
  emptyIntf = EF.Prog "" [] [] [] []
  (newInterface, intMsgs) = genFlatInterface opts modSum env il
  outputInterface = do
    warn opts intMsgs
    EF.writeFlatCurry (optUseSubdir opts) targetFile newInterface

writeAbstractCurry :: Options -> FilePath -> CompilerEnv -> CS.Module -> IO ()
writeAbstractCurry opts fname env modul = do
  when  acyTarget $ AC.writeCurry useSubDir (acyName fname)
                  $ genTypedAbstractCurry env modul
  when uacyTarget $ AC.writeCurry useSubDir (uacyName fname)
                  $ genUntypedAbstractCurry env modul
  where
  acyTarget  = AbstractCurry        `elem` optTargetTypes opts
  uacyTarget = UntypedAbstractCurry `elem` optTargetTypes opts
  useSubDir  = optUseSubdir opts

-- |The 'dump' function writes the selected information to standard output.
doDump :: MonadIO m => Options -> Dump -> m ()
doDump opts (level, env, dump) = when (level `elem` optDumps opts) $ do
  when (optDumpEnv opts) $ liftIO $ putStrLn $ showCompilerEnv opts env
  liftIO $ putStrLn $ unlines [header, replicate (length header) '=', dump]
  where
  header = lookupHeader dumpLevel
  lookupHeader []            = "Unknown dump level " ++ show level
  lookupHeader ((l,_,h):lhs)
    | level == l = h
    | otherwise  = lookupHeader lhs

errModuleFileMismatch :: ModuleIdent -> Message
errModuleFileMismatch mid = posMessage mid $ hsep $ map text
  [ "Module", moduleName mid, "must be in a file"
  , moduleName mid ++ ".(l)curry" ]
