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
>   ( compileModule, checkModuleHeader, simpleCheckModule, checkModule
>   ) where

> import Control.Monad (liftM, unless, when)
> import Data.Maybe (fromMaybe)
> import Text.PrettyPrint (Doc, ($$), text, vcat)

> import qualified Curry.AbstractCurry as AC
> import Curry.Base.MessageMonad
> import Curry.Base.Position
> import Curry.Base.Ident
> import qualified Curry.ExtendedFlat.Type as EF
> import Curry.ExtendedFlat.InterfaceEquality (eqInterface)
> import Curry.Files.Filenames
> import Curry.Files.PathUtils
> import Curry.Syntax as CS

> import Base.CurryTypes (fromQualType)
> import Base.ErrorMessages (errModuleFileMismatch)
> import Base.Messages (abortWith, putErrsLn)
> import Base.Types

> import Env.Eval (evalEnv)
> import Env.Interface
> import Env.TopEnv
> import Env.Value

> import Checks
> import CompilerEnv
> import CompilerOpts
> import Exports (expandInterface, exportInterface)
> import qualified Generators as Gen
> import qualified IL as IL
> import Imports (importModules, qualifyEnv)
> import Interfaces (loadInterfaces)
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
>   -- read and parse module
>   parsed <- (ok . CS.parseModule (not extTarget) fn) `liftM` readModule fn
>   -- check module header
>   let (m, hdrErrs) = checkModuleHeader opts fn parsed
>   unless (null hdrErrs) $ abortWith hdrErrs
>   -- load the imported interfaces into a InterfaceEnv
>   iEnv <- loadInterfaces (optImportPaths opts) m
>   if not withFlat
>      then do
>        let (cEnv, modul, _, warnMsgs) = simpleCheckModule opts iEnv m
>        showWarnings opts warnMsgs
>        -- output the parsed source
>        writeParsed        opts fn modul
>        -- output AbstractCurry
>        writeAbstractCurry opts fn cEnv modul
>      else do
>        -- checkModule checks types, and then transModule introduces new
>        -- functions (by lambda lifting in 'desugar'). Consequence: The
>        -- types of the newly introduced functions are not inferred (hsi)
>        let (cEnv, modul, intf, warnMsgs) = checkModule opts iEnv m
>        showWarnings opts warnMsgs
>        writeParsed        opts fn modul
>        writeAbstractCurry opts fn cEnv modul
>        let (cEnv', il, dumps) = transModule fcyTarget cEnv modul
>        -- dump intermediate results
>        mapM_ (doDump opts) dumps
>        -- generate target code
>        let modSum = summarizeModule (tyConsEnv cEnv') intf modul
>        writeFlat opts fn cEnv' modSum il
>   where
>     fcyTarget = FlatCurry         `elem` optTargetTypes opts
>     xmlTarget = FlatXml           `elem` optTargetTypes opts
>     extTarget = ExtendedFlatCurry `elem` optTargetTypes opts
>     withFlat  = or [fcyTarget, xmlTarget, extTarget]

> checkModuleHeader :: Options -> FilePath -> Module -> (Module, [String])
> checkModuleHeader opts fn = checkModuleId fn
>                           . importPrelude opts
>                           . patchModuleId fn

> -- |Check whether the 'ModuleIdent' and the 'FilePath' fit together
> checkModuleId :: FilePath -> Module -> (Module, [String])
> checkModuleId fn m@(Module mid _ _ _)
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

> importPrelude :: Options -> Module -> Module
> importPrelude opts m@(Module mid es is ds)
>     -- the Prelude itself
>   | mid == preludeMIdent          = m
>     -- disabled by compiler option
>   | noImpPrelude                  = m
>     -- already imported
>   | preludeMIdent `elem` imported = m
>     -- let's add it!
>   | otherwise                     = Module mid es (preludeImp : is) ds
>   where
>     noImpPrelude = NoImplicitPrelude `elem` optExtensions opts
>     preludeImp   = ImportDecl NoPos preludeMIdent
>                    False   -- qualified?
>                    Nothing -- no alias
>                    Nothing -- no selection of types, functions, etc.
>     imported     = [imp | (ImportDecl _ imp _ _ _) <- is]

\end{verbatim}
A module which doesn't contain a \texttt{module ... where} declaration
obtains its filename as module identifier (unlike the definition in
Haskell and original MCC where a module obtains \texttt{main}).
\begin{verbatim}

> patchModuleId :: FilePath -> Module -> Module
> patchModuleId fn m@(Module mid es is ds)
>   | mid == mainMIdent
>     = Module (mkMIdent [takeBaseName fn]) es is ds
>   | otherwise
>     = m

> -- |
> simpleCheckModule :: Options -> InterfaceEnv -> Module
>   -> (CompilerEnv, Module, Interface, [Message])
> simpleCheckModule opts mEnv (Module m es is ds)
>   = (cEnv, modul, intf, warnMsgs)
>   where
>     -- add information of imported modules
>     env = importModules opts m mEnv is
>     -- check for warnings
>     warnMsgs = warnCheck env is ds
>     -- check kinds, syntax, precedence
>     (ds', env2) = uncurry qual
>                    $ uncurry precCheck
>                    $ uncurry (syntaxCheck opts)
>                    $ uncurry kindCheck
>                      (ds, env)
>     modul = Module m es is ds' -- expandInterface env2 $ Module m es is ds'
>     cEnv  = qualifyEnv opts mEnv env2
>     intf  = exportInterface cEnv modul

> checkModule :: Options -> InterfaceEnv -> Module
>   -> (CompilerEnv, Module, Interface, [Message])
> checkModule opts mEnv (Module m es is ds) = (cEnv, modul, intf, warnMsgs)
>   where
>     -- add information of imported modules
>     env = importModules opts m mEnv is
>     -- check for warnings
>     warnMsgs = warnCheck env is ds
>     -- check kinds, syntax, precedence, types
>     (ds', env2) = uncurry qual
>                    $ uncurry typeCheck
>                    $ uncurry precCheck
>                    $ uncurry (syntaxCheck opts)
>                    $ uncurry kindCheck
>                      (ds, env)
>     modul  = expandInterface env2 $ Module m es is ds'
>     cEnv   = qualifyEnv opts mEnv env2
>     intf   = exportInterface cEnv modul

> -- |Translate FlatCurry into the intermediate language 'IL'
> transModule :: Bool -> CompilerEnv -> Module
>             -> (CompilerEnv, IL.Module, [(DumpLevel, Doc)])
> transModule flat' env mdl@(Module m es is ds) = (env5, ilCaseComp, dumps)
>   where
>     env0 = env { evalAnnotEnv = evalEnv ds }
>     (desugared , env1) = desugar (Module m es is ds) env0
>     (simplified, env2) = simplify flat' desugared env1
>     (lifted    , env3) = lift simplified env2
>     (il        , env4) = ilTrans flat' lifted env3
>     (ilCaseComp, env5) = completeCase il env4
>     dumps = [ (DumpRenamed   , ppModule    mdl       )
>             , (DumpTypes     , ppTypes     env       )
>             , (DumpDesugared , ppModule    desugared )
>             , (DumpSimplified, ppModule    simplified)
>             , (DumpLifted    , ppModule    lifted    )
>             , (DumpIL        , IL.ppModule il        )
>             , (DumpCase      , IL.ppModule ilCaseComp)
>             ]

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

> writeFlat :: Options -> FilePath -> CompilerEnv -> ModuleSummary
>           -> IL.Module -> IO ()
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
>     (prog, msgs) = Gen.genFlatCurry opts modSum env il

> writeInterface :: Options -> FilePath -> CompilerEnv -> ModuleSummary
>                -> IL.Module -> IO ()
> writeInterface opts fn env modSum il
>   | optForce opts = outputInterface
>   | otherwise     = do
>       mfint <- EF.readFlatInterface targetFile
>       let oldInterface = fromMaybe emptyIntf mfint
>       when (mfint == mfint) $ return () -- necessary to close file -- TODO
>       unless (oldInterface `eqInterface` newInterface) $ outputInterface
>   where
>     targetFile = flatIntName fn
>     emptyIntf = EF.Prog "" [] [] [] []
>     (newInterface, intMsgs) = Gen.genFlatInterface opts modSum env il
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

> writeAbstractCurry :: Options -> FilePath -> CompilerEnv -> Module -> IO ()
> writeAbstractCurry opts fname env modul = do
>   when  acyTarget $ AC.writeCurry useSubDir (acyName fname)
>                   $ Gen.genTypedAbstractCurry env modul
>   when uacyTarget $ AC.writeCurry useSubDir (uacyName fname)
>                   $ Gen.genUntypedAbstractCurry env modul
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
> doDump opts (dl, x) = when (dl `elem` optDumps opts) $ print
>   (text hd $$ text (replicate (length hd) '=') $$ x)
>   where hd = dumpHeader dl

> dumpHeader :: DumpLevel -> String
> dumpHeader DumpRenamed    = "Module after renaming"
> dumpHeader DumpTypes      = "Types"
> dumpHeader DumpDesugared  = "Source code after desugaring"
> dumpHeader DumpSimplified = "Source code after simplification"
> dumpHeader DumpLifted     = "Source code after lifting"
> dumpHeader DumpIL         = "Intermediate code"
> dumpHeader DumpCase       = "Intermediate code after case simplification"

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: CompilerEnv -> Doc
> ppTypes env = ppTypes' (moduleIdent env) (localBindings $ valueEnv env)
>   where
>   ppTypes' :: ModuleIdent -> [(Ident, ValueInfo)] -> Doc
>   ppTypes' m = vcat . map (ppIDecl . mkDecl) . filter (isValue . snd)
>     where mkDecl (v, Value _ (ForAll _ ty)) =
>             IFunctionDecl undefined (qualify v) (arrowArity ty)
>                          (fromQualType m ty)
>           mkDecl _ = error "Modules.ppTypes.mkDecl: no pattern match"
>           isValue (DataConstructor _ _) = False
>           isValue (NewtypeConstructor _ _) = False
>           isValue (Value _ _) = True
>           isValue (Label _ _ _) = False

\end{verbatim}
