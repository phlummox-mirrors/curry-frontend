{- |
    Module      :  $Header$
    Description :  Compilation of a single module
    Copyright   :  (c) 1999-2004, Wolfgang Lux
                       2005, Martin Engelke (men@informatik.uni-kiel.de)
                       2007, Sebastian Fischer (sebf@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module controls the compilation of modules.
-}

module Modules
  ( compileModule, loadModule, checkModuleHeader, checkModule, writeOutput
  ) where

import Control.Monad (unless, when)
import Data.Maybe (fromMaybe)
import Text.PrettyPrint
import System.IO.Unsafe

import Curry.Base.Ident
import Curry.Base.Message (runMsg)
import Curry.Base.Position
import Curry.ExtendedFlat.InterfaceEquality (eqInterface)
import Curry.Files.Filenames
import Curry.Files.PathUtils

import Base.Messages
  (Message, message, posMessage, warn, abortWithMessages)

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
import Interfaces
import ModuleSummary
import Transformations

-- The function 'compileModule' is the main entry-point of this
-- module for compiling a Curry source module. Depending on the command
-- line options it will emit either C code or FlatCurry code (standard
-- or in XML
-- representation) or AbstractCurry code (typed, untyped or with type
-- signatures) for the module. Usually the first step is to
-- check the module. Then the code is translated into the intermediate
-- language. If necessary, this phase will also update the module's
-- interface file. The resulting code then is either written out (in
-- FlatCurry or XML format) or translated further into C code.
-- The untyped  AbstractCurry representation is written
-- out directly after parsing and simple checking the source file.
-- The typed AbstractCurry code is written out after checking the module.
--
-- The compiler automatically loads the prelude when compiling any
-- module, except for the prelude itself, by adding an appropriate import
-- declaration to the module.
--
-- Since this modified version of the Muenster Curry Compiler is used
-- as a frontend for PAKCS, all functions for evaluating goals and generating
-- C code are obsolete and commented out.

compileModule :: Options -> FilePath -> IO ()
compileModule opts fn = do
  loaded <- loadModule opts fn
  -- write parsed output always if requested, also if the following checks fail
  when (Parsed `elem` optTargetTypes opts) $ do 
    let (env, mdl) = loaded
    writeParsed opts fn mdl
    -- dump parse tree if requested
    when (DumpParsed `elem` optDumps opts) $ 
      doDump opts (DumpParsed, env, 
        (if optDumpRaw opts then show else show . CS.ppModule) mdl)
  -- do checks only if a different output than the parse tree is requested 
  when (not . null $ filter (/= Parsed) (optTargetTypes opts))
    (case checkModule opts loaded of
      CheckFailed errs -> abortWithMessages errs
      CheckSuccess (env, mdl, dumps) -> do
        warn opts $ warnCheck env mdl
        mapM_ (doDump opts) dumps
        writeOutput opts fn (env, mdl))

writeOutput :: Options -> FilePath -> (CompilerEnv, CS.Module) -> IO ()
writeOutput opts fn (env, modul) = do
  writeParsed        opts fn     modul
  writeAbstractCurry opts fn env modul
  when withFlat $ do
    -- checkModule checks types, and then transModule introduces new
    -- functions (by lambda lifting in 'desugar'). Consequence: The
    -- types of the newly introduced functions are not inferred (hsi)
    let (env2, il, dumps) = transModule opts env modul
    -- dump intermediate results
    mapM_ (doDump opts) dumps
    -- generate target code
    let intf = exportInterface env2 modul
    let modSum = summarizeModule (tyConsEnv env2) intf modul
    writeFlat opts fn env2 modSum il
  where
  withFlat = any (`elem` optTargetTypes opts)
              [FlatCurry, FlatXml, ExtendedFlatCurry]

-- ---------------------------------------------------------------------------
-- Loading a module
-- ---------------------------------------------------------------------------

loadModule :: Options -> FilePath -> IO (CompilerEnv, CS.Module)
loadModule opts fn = do
  -- read module
  mbSrc <- readModule fn
  case mbSrc of
    Nothing  -> abortWithMessages [message $ text $ "Missing file: " ++ fn] -- TODO
    Just src -> do
      -- parse module
      case runMsg $ CS.parseModule fn src of
        Left err -> abortWithMessages [err]
        Right (parsed, _) -> do
          -- check module header
          let (mdl, hdrErrs) = checkModuleHeader opts fn parsed
          unless (null hdrErrs) $ abortWithMessages hdrErrs -- TODO
          -- load the imported interfaces into an InterfaceEnv
          (iEnv, intfErrs) <- loadInterfaces (optImportPaths opts) mdl
          unless (null intfErrs) $ abortWithMessages intfErrs -- TODO
          -- add information of imported modules
          let (env, impErrs) = importModules opts mdl iEnv
          unless (null impErrs) $ abortWithMessages impErrs -- TODO
          return (env, mdl)

checkModuleHeader :: Options -> FilePath -> CS.Module -> (CS.Module, [Message])
checkModuleHeader opts fn = checkModuleId fn
                          . importPrelude opts fn
                          . CS.patchModuleId fn

-- |Check whether the 'ModuleIdent' and the 'FilePath' fit together
checkModuleId :: FilePath -> CS.Module -> (CS.Module, [Message])
checkModuleId fn m@(CS.Module mid _ _ _)
  | last (midQualifiers mid) == takeBaseName fn
  = (m, [])
  | otherwise
  = (m, [errModuleFileMismatch mid])

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

-- ---------------------------------------------------------------------------
-- Checking a module
-- ---------------------------------------------------------------------------

-- TODO: The order of the checks should be improved!
-- TODO (2012-01-05, bjp): The export specification check for untyped
--   AbstractCurry is deactivated as it requires the value information
--   collected by the type checker.
checkModule :: Options -> (CompilerEnv, CS.Module)
            -> CheckResult (CompilerEnv, CS.Module, [Dump])
checkModule opts (env, mdl) = do
  (env1,  kc) <- kindCheck env mdl -- should be only syntax checking ?
  (env2,  sc) <- syntaxCheck opts env1 kc
  (env3,  pc) <- precCheck        env2 sc
  -- (env4, tcc) <- typeClassesCheck env3 pc
  (env4, tcc) <- unsafePerformIO (doDump opts (DumpPrecChecked, env3, show' CS.ppModule pc) >> return (typeClassesCheck env3 pc) ) 
  (env5,  tc) <- if withTypeCheck
                   -- then typeCheck env4 tcc
                   then unsafePerformIO (doDump opts (DumpTypeClassesChecked, env4, show' CS.ppModule tcc) >> return (typeCheck env4 tcc) )
                   else return (env4, tcc)
  (env6,  ec) <- if withTypeCheck 
                   then exportCheck env5 tc
                   else return (env5, tc)
  (env7,  ql) <- return $ qual opts env6 ec
  let dumps = [ (DumpParsed            , env , show' CS.ppModule mdl)
              , (DumpKindChecked       , env1, show' CS.ppModule kc)
              , (DumpSyntaxChecked     , env2, show' CS.ppModule sc)
              , (DumpPrecChecked       , env3, show' CS.ppModule pc)
              , (DumpTypeClassesChecked, env4, show' CS.ppModule tcc)
              , (DumpTypeChecked       , env5, show' CS.ppModule tc)
              , (DumpExportChecked     , env6, show' CS.ppModule ec)
              , (DumpQualified         , env7, show' CS.ppModule ql)
              ]
  return (env7, ql, dumps)
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

-- The functions \texttt{genFlat} and \texttt{genAbstract} generate
-- flat and abstract curry representations depending on the specified option.
-- If the interface of a modified Curry module did not change, the
-- corresponding file name will be returned within the result of 'genFlat'
-- (depending on the compiler flag "force") and other modules importing this
-- module won't be dependent on it any longer.

-- |Output the parsed 'Module' on request
writeParsed :: Options -> FilePath -> CS.Module -> IO ()
writeParsed opts fn modul = when srcTarget $
  writeModule useSubDir targetFile source
  where
  srcTarget  = Parsed `elem` optTargetTypes opts
  useSubDir  = optUseSubdir opts
  targetFile = fromMaybe (sourceRepName fn) (optOutput opts)
  source     = CS.showModule modul

writeFlat :: Options -> FilePath -> CompilerEnv -> ModuleSummary -> IL.Module
          -> IO ()
writeFlat opts fn env modSum il = do
  when (extTarget || fcyTarget) $ do
    writeFlatCurry opts fn env modSum il
    writeInterface opts fn env modSum il
  when (xmlTarget) $ writeXML opts fn modSum il
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
writeXML :: Options -> FilePath -> ModuleSummary -> IL.Module -> IO ()
writeXML opts fn modSum il = writeModule useSubDir (xmlName fn) curryXml
  where
  useSubDir = optUseSubdir opts
  curryXml  = shows (IL.xmlModule (interface modSum) (infixDecls modSum) il) "\n"

writeInterface :: Options -> FilePath -> CompilerEnv -> ModuleSummary
               -> IL.Module -> IO ()
writeInterface opts fn env modSum il
  | not (optInterface opts) = return ()
  | optForce opts           = outputInterface
  | otherwise               = do
      mfint <- EF.readFlatInterface targetFile
      let oldInterface = fromMaybe emptyIntf mfint
      when (mfint == mfint) $ return () -- necessary to close file -- TODO
      unless (oldInterface `eqInterface` newInterface) $ outputInterface
  where
  targetFile = flatIntName fn
  emptyIntf = EF.Prog "" [] [] [] [] -- Nothing
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
doDump :: Options -> Dump -> IO ()
doDump opts (level, env, dump) = when (level `elem` optDumps opts) $ do
  when (optDumpEnv opts) $ putStrLn $ showCompilerEnv opts env
  putStrLn $ unlines [header, replicate (length header) '=', dump]
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
