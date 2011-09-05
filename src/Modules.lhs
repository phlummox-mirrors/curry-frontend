> {- |
>     Module      :  $Header$
>     Description :  Cumputation of export interface
>     Copyright   :  (c) 1999-2004, Wolfgang Lux
>                        2005, Martin Engelke (men@informatik.uni-kiel.de)
>                        2007, Sebastian Fischer (sebf@informatik.uni-kiel.de)
>                        2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
>     License     :  OtherLicense
>
>     Maintainer  :  bjp@informatik.uni-kiel.de
>     Stability   :  experimental
>     Portability :  portable
>
>     This module provides the computation of the exported interface of a
>     compiled module.
> -}

\nwfilename{Modules.lhs}
\section{Modules}
This module controls the compilation of modules.
\begin{verbatim}

> module Modules
>   ( compileModule, loadModule, checkModuleHeader, checkModule
>   ) where

> import Control.Monad (liftM, unless, when)
> import Data.Maybe (fromMaybe)
> import Text.PrettyPrint (Doc)

> import Curry.Base.MessageMonad
> import Curry.Base.Position
> import Curry.Base.Ident
> import Curry.ExtendedFlat.InterfaceEquality (eqInterface)
> import Curry.Files.Filenames
> import Curry.Files.PathUtils

> import Base.ErrorMessages (errModuleFileMismatch)
> import Base.Messages (abortWith, putErrsLn)

> import Env.Eval (evalEnv)
> import Env.Value (ppTypes)

> -- source representations
> import qualified Curry.AbstractCurry as AC
> import qualified Curry.ExtendedFlat.Type as EF
> import qualified Curry.Syntax as CS
> import qualified IL as IL

> import Checks
> import CompilerEnv
> import CompilerOpts
> import Exports
> import Generators
> import Imports
> import Interfaces
> import ModuleSummary
> import Transformations

\end{verbatim}
The function \texttt{compileModule} is the main entry-point of this
module for compiling a Curry source module. Depending on the command
line options it will emit either C code or FlatCurry code (standard
or in XML
representation) or AbstractCurry code (typed, untyped or with type
signatures) for the module. Usually the first step is to
check the module. Then the code is translated into the intermediate
language. If necessary, this phase will also update the module's
interface file. The resulting code then is either written out (in
FlatCurry or XML format) or translated further into C code.
The untyped  AbstractCurry representation is written
out directly after parsing and simple checking the source file.
The typed AbstractCurry code is written out after checking the module.

The compiler automatically loads the prelude when compiling any
module, except for the prelude itself, by adding an appropriate import
declaration to the module.

Since this modified version of the Muenster Curry Compiler is used
as a frontend for PAKCS, all functions for evaluating goals and generating C
code are obsolete and commented out.
\begin{verbatim}

> compileModule :: Options -> FilePath -> IO ()
> compileModule opts fn = do
>   (env, modul, intf, warnings) <- uncurry (checkModule opts) `liftM` loadModule opts fn
>   showWarnings opts $ warnings
>   writeParsed        opts fn     modul
>   writeAbstractCurry opts fn env modul
>   when withFlat $ do
>     -- checkModule checks types, and then transModule introduces new
>     -- functions (by lambda lifting in 'desugar'). Consequence: The
>     -- types of the newly introduced functions are not inferred (hsi)
>     let (env2, il, dumps) = transModule opts env modul
>     -- dump intermediate results
>     mapM_ (doDump opts) dumps
>     -- generate target code
>     let modSum = summarizeModule (tyConsEnv env2) intf modul
>     writeFlat opts fn env2 modSum il
>   where
>     withFlat = any (`elem` optTargetTypes opts)
>                    [FlatCurry, FlatXml, ExtendedFlatCurry]

-- ---------------------------------------------------------------------------
-- Loading a module
-- ---------------------------------------------------------------------------

> loadModule :: Options -> FilePath -> IO (CompilerEnv, CS.Module)
> loadModule opts fn = do
>   -- read and parse module
>   parsed <- (ok . CS.parseModule (not extTarget) fn) `liftM` readModule fn
>   -- check module header
>   let (mdl, hdrErrs) = checkModuleHeader opts fn parsed
>   unless (null hdrErrs) $ abortWith hdrErrs
>   -- load the imported interfaces into an InterfaceEnv
>   iEnv <- loadInterfaces (optImportPaths opts) mdl
>   -- add information of imported modules
>   let env = importModules opts mdl iEnv
>   return (env, mdl)
>   where extTarget = ExtendedFlatCurry `elem` optTargetTypes opts

> checkModuleHeader :: Options -> FilePath -> CS.Module -> (CS.Module, [String])
> checkModuleHeader opts fn = checkModuleId fn
>                           . importPrelude opts
>                           . patchModuleId fn

> -- |Check whether the 'ModuleIdent' and the 'FilePath' fit together
> checkModuleId :: FilePath -> CS.Module -> (CS.Module, [String])
> checkModuleId fn m@(CS.Module mid _ _ _)
>   | last (moduleQualifiers mid) == takeBaseName fn
>   = (m, [])
>   | otherwise
>   = (m, [errModuleFileMismatch mid])

\end{verbatim}
An implicit import of the prelude is added to the declarations of
every module, except for the prelude itself, or when the import is disabled
by a compiler option. If no explicit import for the prelude is present,
the prelude is imported unqualified, otherwise a qualified import is added.
\begin{verbatim}

> importPrelude :: Options -> CS.Module -> CS.Module
> importPrelude opts m@(CS.Module mid es is ds)
>     -- the Prelude itself
>   | mid == preludeMIdent          = m
>     -- disabled by compiler option
>   | noImpPrelude                  = m
>     -- already imported
>   | preludeMIdent `elem` imported = m
>     -- let's add it!
>   | otherwise                     = CS.Module mid es (preludeImp : is) ds
>   where
>     noImpPrelude = NoImplicitPrelude `elem` optExtensions opts
>     preludeImp   = CS.ImportDecl NoPos preludeMIdent
>                    False   -- qualified?
>                    Nothing -- no alias
>                    Nothing -- no selection of types, functions, etc.
>     imported     = [imp | (CS.ImportDecl _ imp _ _ _) <- is]

\end{verbatim}
A module which doesn't contain a \texttt{module ... where} declaration
obtains its filename as module identifier (unlike the definition in
Haskell and original MCC where a module obtains \texttt{main}).
\begin{verbatim}

> patchModuleId :: FilePath -> CS.Module -> CS.Module
> patchModuleId fn m@(CS.Module mid es is ds)
>   | mid == mainMIdent
>     = CS.Module (mkMIdent [takeBaseName fn]) es is ds
>   | otherwise
>     = m

-- ---------------------------------------------------------------------------
-- Checking a module
-- ---------------------------------------------------------------------------

> checkModule :: Options -> CompilerEnv -> CS.Module
>             -> (CompilerEnv, CS.Module, CS.Interface, [Message])
> checkModule opts env mdl = (env', mdl', intf, warnings)
>   where
>     warnings = warnCheck env mdl
>     intf = exportInterface env' mdl'
>     (env', mdl') = qualifyE $ expand $ uncurry qual
>                  $ (if withFlat then uncurry typeCheck else id)
>                  $ uncurry precCheck
>                  $ uncurry (syntaxCheck opts)
>                  $ uncurry kindCheck
>                    (env, mdl)
>     expand   (e, m) = if withFlat then (e, expandInterface e m) else (e, m)
>     qualifyE (e, m) = (qualifyEnv opts e, m)
>     withFlat = any (`elem` optTargetTypes opts)
>                [FlatCurry, FlatXml, ExtendedFlatCurry]

-- ---------------------------------------------------------------------------
-- Translating a module
-- ---------------------------------------------------------------------------

> -- |Translate FlatCurry into the intermediate language 'IL'
> transModule :: Options -> CompilerEnv -> CS.Module
>             -> (CompilerEnv, IL.Module, [(DumpLevel, Doc)])
> transModule opts env mdl = (env5, ilCaseComp, dumps)
>   where
>     flat' = FlatCurry `elem` optTargetTypes opts
>     env0 = env { evalAnnotEnv = evalEnv mdl }
>     (desugared , env1) = desugar        mdl        env0
>     (simplified, env2) = simplify flat' desugared  env1
>     (lifted    , env3) = lift           simplified env2
>     (il        , env4) = ilTrans flat'  lifted     env3
>     (ilCaseComp, env5) = completeCase   il         env4
>     dumps = [ (DumpRenamed   , CS.ppModule    mdl         )
>             , (DumpTypes     , ppTypes     (moduleIdent env) (valueEnv env))
>             , (DumpDesugared , CS.ppModule    desugared   )
>             , (DumpSimplified, CS.ppModule    simplified  )
>             , (DumpLifted    , CS.ppModule    lifted    )
>             , (DumpIL        , IL.ppModule il        )
>             , (DumpCase      , IL.ppModule ilCaseComp)
>             ]

-- ---------------------------------------------------------------------------
-- Writing output
-- ---------------------------------------------------------------------------

\end{verbatim}
The functions \texttt{genFlat} and \texttt{genAbstract} generate
flat and abstract curry representations depending on the specified option.
If the interface of a modified Curry module did not change, the corresponding
file name will be returned within the result of \texttt{genFlat} (depending
on the compiler flag "force") and other modules importing this module won't
be dependent on it any longer.
\begin{verbatim}

> -- |Output the parsed 'Module' on request
> writeParsed :: Options -> FilePath -> CS.Module -> IO ()
> writeParsed opts fn modul = when srcTarget $
>   writeModule useSubDir targetFile source
>   where
>     srcTarget  = Parsed `elem` optTargetTypes opts
>     useSubDir  = optUseSubdir opts
>     targetFile = fromMaybe (sourceRepName fn) (optOutput opts)
>     source     = CS.showModule modul

> writeFlat :: Options -> FilePath -> CompilerEnv -> ModuleSummary -> IL.Module -> IO ()
> writeFlat opts fn env modSum il = do
>   writeFlatCurry opts fn env modSum il
>   writeInterface opts fn env modSum il
>   writeXML       opts fn     modSum il

> -- |Export an 'IL.Module' into a FlatCurry file
> writeFlatCurry :: Options -> FilePath -> CompilerEnv -> ModuleSummary
>                -> IL.Module -> IO ()
> writeFlatCurry opts fn env modSum il = do
>   when (extTarget || fcyTarget) $ showWarnings opts msgs
>   when extTarget $ EF.writeExtendedFlat useSubDir (extFlatName fn) prog
>   when fcyTarget $ EF.writeFlatCurry    useSubDir (flatName fn)    prog
>   where
>     extTarget    = ExtendedFlatCurry `elem` optTargetTypes opts
>     fcyTarget    = FlatCurry         `elem` optTargetTypes opts
>     useSubDir    = optUseSubdir opts
>     (prog, msgs) = genFlatCurry opts modSum env il

> writeInterface :: Options -> FilePath -> CompilerEnv -> ModuleSummary
>                -> IL.Module -> IO ()
> writeInterface opts fn env modSum il
>   | not (optInterface opts) = return ()
>   | optForce opts           = outputInterface
>   | otherwise               = do
>       mfint <- EF.readFlatInterface targetFile
>       let oldInterface = fromMaybe emptyIntf mfint
>       when (mfint == mfint) $ return () -- necessary to close file -- TODO
>       unless (oldInterface `eqInterface` newInterface) $ outputInterface
>   where
>     targetFile = flatIntName fn
>     emptyIntf = EF.Prog "" [] [] [] []
>     (newInterface, intMsgs) = genFlatInterface opts modSum env il
>     outputInterface = do
>       showWarnings opts intMsgs
>       EF.writeFlatCurry (optUseSubdir opts) targetFile newInterface

> -- |Export an 'IL.Module' into an XML file
> writeXML :: Options -> FilePath -> ModuleSummary -> IL.Module -> IO ()
> writeXML opts fn modSum il = when xmlTarget $
>   writeModule useSubDir targetFile curryXml
>   where
>     xmlTarget  = FlatXml `elem` optTargetTypes opts
>     useSubDir  = optUseSubdir opts
>     targetFile = fromMaybe (xmlName fn) (optOutput opts)
>     curryXml   = shows (IL.xmlModule modSum il) "\n"

> writeAbstractCurry :: Options -> FilePath -> CompilerEnv -> CS.Module -> IO ()
> writeAbstractCurry opts fname env modul = do
>   when  acyTarget $ AC.writeCurry useSubDir (acyName fname)
>                   $ genTypedAbstractCurry env modul
>   when uacyTarget $ AC.writeCurry useSubDir (uacyName fname)
>                   $ genUntypedAbstractCurry env modul
>   where
>     acyTarget  = AbstractCurry        `elem` optTargetTypes opts
>     uacyTarget = UntypedAbstractCurry `elem` optTargetTypes opts
>     useSubDir  = optUseSubdir opts

> showWarnings :: Options -> [Message] -> IO ()
> showWarnings opts msgs = when (optWarn opts)
>                        $ putErrsLn $ map showWarning msgs

\end{verbatim}
The \texttt{doDump} function writes the selected information to the
standard output.
\begin{verbatim}

> doDump :: Options -> (DumpLevel, Doc) -> IO ()
> doDump opts (level, dump) = when (level `elem` optDumps opts) $ putStrLn $
>   unlines [header, replicate (length header) '=', show dump]
>   where header = dumpHeader level

> dumpHeader :: DumpLevel -> String
> dumpHeader DumpRenamed    = "Module after renaming"
> dumpHeader DumpTypes      = "Types"
> dumpHeader DumpDesugared  = "Source code after desugaring"
> dumpHeader DumpSimplified = "Source code after simplification"
> dumpHeader DumpLifted     = "Source code after lifting"
> dumpHeader DumpIL         = "Intermediate code"
> dumpHeader DumpCase       = "Intermediate code after case completion"

\end{verbatim}
