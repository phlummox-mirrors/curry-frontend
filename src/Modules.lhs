% -*- LaTeX -*-
% $Id: Modules.lhs,v 1.84 2004/02/10 17:46:07 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Modules.lhs}
\section{Modules}
This module controls the compilation of modules.
\begin{verbatim}

> module Modules(compileModule,compileGoal,typeGoal) where
> import Base
> import Unlit(unlit)
> import CurryParser(parseSource,parseInterface,parseGoal)
> import KindCheck(kindCheck,kindCheckGoal)
> import SyntaxCheck(syntaxCheck,syntaxCheckGoal)
> import PrecCheck(precCheck,precCheckGoal)
> import TypeCheck(typeCheck,typeCheckGoal)
> import IntfCheck(intfCheck,fixInterface,intfEquiv)
> import Imports(importInterface,importInterfaceIntf,importUnifyData)
> import Exports(expandInterface,exportInterface)
> import Eval(evalEnv,evalEnvGoal)
> import Qual(qual,qualGoal)
> import Desugar(desugar,desugarGoal)
> import Simplify(simplify)
> import Lift(lift)
> import CurryInfo
> import FlatCurry
> import qualified IL
> import ILTrans(ilTrans,ilTransIntf)
> import ILLift(liftProg)
> import ILxml(xmlModule)
> import IL2FlatCurry
> import DTransform(dTransform,dAddMain)
> import ILCompile(camCompile,camCompileData,fun)
> import qualified CamPP(ppModule)
> import CGen(genMain,genEntry,genModule,genSplitModule)
> import CCode(CFile,mergeCFile)
> import CPretty(ppCFile)
> import CurryPP(ppModule,ppInterface,ppIDecl,ppGoal)
> import qualified ILPP(ppModule)
> import Options(Options(..),Dump(..))
> import CaseCompletion
> import PathUtils
> import List
> import IO
> import Maybe
> import Monad
> import Pretty
> import Error
> import Env
> import TopEnv
> import Typing

\end{verbatim}
The function \texttt{compileModule} is the main entry-point of this
module for compiling a Curry source module. Depending on the command
line options it will emit either C code or FlatCurry code in XML
representation for the module. In both cases, the first step is to
check the module and translate the code into the intermediate
language. If necessary, this phase will also update the module's
interface file. The resulting code then is either written out -- in
the XML format -- or translated further into C code.

The compiler automatically loads the prelude when compiling any
module, except for the prelude itself, by adding an appropriate import
declaration to the module. However, the compiler does not load the
\texttt{DebugPrelude} when the debugging transformation is used, even
though entities from this module are entered into the code. We do not
load the \texttt{DebugPrelude} because it \emph{necessarily} imports
the prelude and the compiler is not capable of handling mutual
recursion between modules. Fortunately, all information that is needed
to generate C code from the transformed code -- in particular, the
arities of the functions and constructors -- is already available in
the intermediate language code. In addition, the transformed code does
not perform pattern matchings against any of the data constructors
exported from \texttt{DebugPrelude} which cannot be implemented
without the interface file.\footnote{The interface declarations were
needed in order to determine the tag number of each data constructor.
With the help of the tag numbers, the compiler generates indexed
switches instead of nested if-then-else cascades for the pattern
matching code.}
\begin{verbatim}

> compileModule :: Options -> FilePath -> IO ()
> compileModule opts fn =
>   do
>     m <- liftM (parseModule flat fn) (readFile fn)
>     mEnv <- loadInterfaces (importPath opts) m
>     let (tyEnv,m',intf) = checkModule mEnv m
>         (il,dumps) =
>           transModule flat (debug opts) (trusted opts) mEnv tyEnv m'
>         (ccode,dumps') = ccodeModule (splitCode opts) mEnv il
>         ccode' = compileDefaultGoal (debug opts) mEnv intf
>         il' = completeCase mEnv il
>     mapM_ (doDump opts) 
>           (dumps ++ if flat || abstract || xml then [] else dumps')
>     unless (noInterface opts) (updateInterface fn intf)
>     if flat || abstract || xml then genCurry opts fn mEnv m' il'
>        else writeCode (output opts) fn (maybe ccode (merge ccode) ccode')
>   where abstract = abstractCurry opts
>         flat     = flatCurry opts
>         xml      = flatXML opts
>         merge (Left cf1) cf2 = Left (mergeCFile cf1 cf2)
>         merge (Right cfs) cf = Right (cf : cfs)

> parseModule :: Bool -> FilePath -> String -> Module
> parseModule flat fn =
>   importPrelude fn . ok . parseSource flat fn . unlitLiterate fn

> loadInterfaces :: [FilePath] -> Module -> IO ModuleEnv
> loadInterfaces paths (Module m _ ds) =
>   foldM (loadInterface paths [m]) emptyEnv
>         [(p,m) | ImportDecl p m _ _ _ <- ds]

> checkModule :: ModuleEnv -> Module -> (ValueEnv,Module,Interface)
> checkModule mEnv (Module m es ds) =
>   (tyEnv'',modul,exportInterface modul pEnv'' tcEnv'' tyEnv'')
>   where (impDs,topDs) = partition isImportDecl ds
>         (pEnv,tcEnv,tyEnv) = importModules mEnv impDs
>         (pEnv',topDs') = precCheck m pEnv $ syntaxCheck m tyEnv
>                                           $ kindCheck m tcEnv topDs
>         (tcEnv',tyEnv') = typeCheck m tcEnv tyEnv topDs'
>         ds' = impDs ++ qual tyEnv' topDs'
>         modul = expandInterface (Module m es ds') tcEnv' tyEnv'
>         (pEnv'',tcEnv'',tyEnv'') = qualifyEnv mEnv pEnv' tcEnv' tyEnv'

> transModule :: Bool -> Bool -> Bool -> ModuleEnv -> ValueEnv -> Module
>             -> (IL.Module,[(Dump,Doc)])
> transModule flat debug trusted mEnv tyEnv (Module m es ds) = (ilDbg,dumps)
>   where topDs = filter (not . isImportDecl) ds
>         evEnv = evalEnv topDs
>         (desugared,tyEnv') = desugar tyEnv (Module m es topDs)
>         (simplified,tyEnv'') = simplify flat tyEnv' evEnv desugared
>         (lifted,tyEnv''',evEnv') = lift tyEnv'' evEnv simplified
>         il = ilTrans flat tyEnv''' evEnv' lifted
>         ilDbg = if debug then dTransform trusted il else il
>         dumps = [
>             (DumpRenamed,ppModule (Module m es ds)),
>             (DumpTypes,ppTypes m (localBindings tyEnv)),
>             (DumpDesugared,ppModule desugared),
>             (DumpSimplified,ppModule simplified),
>             (DumpLifted,ppModule lifted),
>             (DumpIL,ILPP.ppModule il),
>             (DumpTransformed,ILPP.ppModule ilDbg)
>           ]

> ccodeModule :: Bool -> ModuleEnv -> IL.Module
>             -> (Either CFile [CFile],[(Dump,Doc)])
> ccodeModule split mEnv il = (ccode,dumps)
>   where ilNormal = liftProg il
>         cam = camCompile ilNormal
>         imports = camCompileData (ilImports mEnv il)
>         ccode
>           | split = Right (genSplitModule imports cam)
>           | otherwise = Left (genModule imports cam)
>         dumps = [
>             (DumpNormalized,ILPP.ppModule ilNormal),
>             (DumpCam,CamPP.ppModule cam)
>           ]

> qualifyEnv :: ModuleEnv -> PEnv -> TCEnv -> ValueEnv -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv mEnv pEnv tcEnv tyEnv =
>   (foldr bindQual pEnv' (localBindings pEnv),
>    foldr bindQual tcEnv' (localBindings tcEnv),
>    foldr bindGlobal tyEnv' (localBindings tyEnv))
>   where (pEnv',tcEnv',tyEnv') =
>           foldl importInterface initEnvs (envToList mEnv)
>         importInterface (pEnv,tcEnv,tyEnv) (m,ds) =
>           importInterfaceIntf (Interface m ds) pEnv tcEnv tyEnv
>         bindQual (_,y) = qualBindTopEnv (origName y) y
>         bindGlobal (x,y)
>           | uniqueId x == 0 = bindQual (x,y)
>           | otherwise = bindTopEnv x y

> ilImports :: ModuleEnv -> IL.Module -> [IL.Decl]
> ilImports mEnv (IL.Module _ is _) =
>   concat [ilTransIntf (Interface m ds) | (m,ds) <- envToList mEnv,
>                                          m `elem` is]

> writeXML :: Maybe FilePath -> FilePath -> CurryInfo -> IL.Module -> IO ()
> writeXML tfn sfn fi il = writeFile ofn (showln code)
>   where ofn  = fromMaybe (rootname sfn ++ xmlExt) tfn
>         code = (xmlModule fi il)

> writeFlat :: Maybe FilePath -> FilePath -> CurryInfo -> IL.Module -> IO ()
> writeFlat tfn sfn fi il = writeFlatCurry fname (il2flatCurry fi il)
>   where fname = fromMaybe (rootname sfn ++ flatExt) tfn

> writeCode :: Maybe FilePath -> FilePath -> Either CFile [CFile] -> IO ()
> writeCode tfn sfn (Left cfile) = writeCCode ofn cfile
>   where ofn = fromMaybe (rootname sfn ++ cExt) tfn
> writeCode tfn sfn (Right cfiles) = zipWithM_ (writeCCode . mkFn) [1..] cfiles
>   where prefix = fromMaybe (rootname sfn) tfn
>         mkFn i = prefix ++ show i ++ cExt

> writeCCode :: FilePath -> CFile -> IO ()
> writeCCode fn = writeFile fn . showln . ppCFile

> showln :: Show a => a -> String
> showln x = shows x "\n"

\end{verbatim}
A goal is compiled with respect to a given module. If no module is
specified the Curry prelude is used. The source module has to be
parsed and type checked before the goal can be compiled.  Otherwise
compilation of a goal is similar to that of a module.
\begin{verbatim}

> compileGoal :: Options -> Maybe String -> Maybe FilePath -> IO ()
> compileGoal opts g fn =
>   do
>     (ccode,dumps) <- maybe (return startupCode) goalCode g
>     mapM_ (doDump opts) dumps
>     writeCCode ofn ccode
>   where ofn = fromMaybe (internalError "No filename for startup code")
>                         (output opts)
>         startupCode = (genMain "curry_run",[])
>         goalCode = doCompileGoal (debug opts) (importPath opts) fn

> doCompileGoal :: Bool -> [FilePath] -> Maybe FilePath -> String
>               -> IO (CFile,[(Dump,Doc)])
> doCompileGoal debug paths fn g =
>   do
>     (mEnv,_,ds) <- loadGoalModule paths fn
>     let (tyEnv,g') = checkGoal mEnv ds (ok (parseGoal g))
>         (ccode,dumps) =
>           transGoal debug runGoal mEnv tyEnv (mkIdent "goal") g'
>         ccode' = genMain runGoal
>     return (mergeCFile ccode ccode',dumps)
>   where runGoal = "curry_runGoal"

> typeGoal :: Options -> String -> Maybe FilePath -> IO ()
> typeGoal opts g fn =
>   do
>     (mEnv,m,ds) <- loadGoalModule (importPath opts) fn
>     let (tyEnv,Goal _ e _) = checkGoal mEnv ds (ok (parseGoal g))
>     print (ppType m (typeOf tyEnv e))

> loadGoalModule :: [FilePath] -> Maybe FilePath
>                -> IO (ModuleEnv,ModuleIdent,[Decl])
> loadGoalModule paths fn =
>   do
>     Module m _ ds <- maybe (return emptyModule) parseGoalModule fn
>     mEnv <- loadInterfaces paths (Module m Nothing ds)
>     let (_,_,intf) = checkModule mEnv (Module m Nothing ds)
>     return (bindModule intf mEnv,m,filter isImportDecl ds ++ [importMain m])
>   where emptyModule = importPrelude "" (Module emptyMIdent Nothing [])
>         parseGoalModule fn = liftM (parseModule False fn) (readFile fn)
>         importMain m = ImportDecl (first "") m False Nothing Nothing

> checkGoal :: ModuleEnv -> [Decl] -> Goal -> (ValueEnv,Goal)
> checkGoal mEnv impDs g = (tyEnv'',qualGoal tyEnv' g')
>   where (pEnv,tcEnv,tyEnv) = importModules mEnv impDs
>         g' = precCheckGoal pEnv $ syntaxCheckGoal tyEnv
>                                 $ kindCheckGoal tcEnv g
>         tyEnv' = typeCheckGoal tcEnv tyEnv g'
>         (_,_,tyEnv'') = qualifyEnv mEnv pEnv tcEnv tyEnv'

> transGoal :: Bool -> String -> ModuleEnv -> ValueEnv -> Ident -> Goal
>           -> (CFile,[(Dump,Doc)])
> transGoal debug run mEnv tyEnv goalId g = (ccode,dumps)
>   where qGoalId = qualifyWith emptyMIdent goalId
>         evEnv = evalEnvGoal g
>         (vs,desugared,tyEnv') = desugarGoal debug tyEnv emptyMIdent goalId g
>         (simplified,tyEnv'') = simplify False tyEnv' evEnv desugared
>         (lifted,tyEnv''',evEnv') = lift tyEnv'' evEnv simplified
>         il = ilTrans False tyEnv''' evEnv' lifted
>         ilDbg = if debug then dAddMain goalId (dTransform False il) else il
>         ilNormal = liftProg ilDbg
>         cam = camCompile ilNormal
>         imports = camCompileData (ilImports mEnv ilDbg)
>         ccode =
>           genModule imports cam ++
>           genEntry run (fun qGoalId) (fmap (map name) vs)
>         dumps = [
>             (DumpRenamed,ppGoal g),
>             (DumpTypes,ppTypes emptyMIdent (localBindings tyEnv)),
>             (DumpDesugared,ppModule desugared),
>             (DumpSimplified,ppModule simplified),
>             (DumpLifted,ppModule lifted),
>             (DumpIL,ILPP.ppModule il),
>             (DumpTransformed,ILPP.ppModule ilDbg),
>             (DumpNormalized,ILPP.ppModule ilNormal),
>             (DumpCam,CamPP.ppModule cam)
>           ]

\end{verbatim}
The compiler adds a startup function for the default goal
\texttt{main.main} to the \texttt{main} module. Thus, there is no need
to determine the type of the goal when linking the program.
\begin{verbatim}

> compileDefaultGoal :: Bool -> ModuleEnv -> Interface -> Maybe CFile
> compileDefaultGoal debug mEnv (Interface m ds)
>   | m == mainMIdent && any (qMainId ==) [f | IFunctionDecl _ f _ <- ds] =
>       Just ccode
>   | otherwise = Nothing
>   where qMainId = qualify mainId
>         mEnv' = bindModule (Interface m ds) mEnv
>         (tyEnv,g) =
>           checkGoal mEnv' [ImportDecl (first "") m False Nothing Nothing]
>                     (Goal (first "") (Variable qMainId) [])
>         (ccode,_) = transGoal debug "curry_run" mEnv' tyEnv mainId g

\end{verbatim}
The function \texttt{importModules} brings the declarations of all
imported modules into scope for the current module.
\begin{verbatim}

> importModules :: ModuleEnv -> [Decl] -> (PEnv,TCEnv,ValueEnv)
> importModules mEnv ds = (pEnv,importUnifyData tcEnv,tyEnv)
>   where (pEnv,tcEnv,tyEnv) = foldl importModule initEnvs ds
>         importModule (pEnv,tcEnv,tyEnv) (ImportDecl p m q asM is) =
>           case lookupModule m mEnv of
>             Just ds -> importInterface p (fromMaybe m asM) q is
>                                        (Interface m ds) pEnv tcEnv tyEnv
>             Nothing -> internalError "importModule"
>         importModule (pEnv,tcEnv,tyEnv) _ = (pEnv,tcEnv,tyEnv)

> initEnvs :: (PEnv,TCEnv,ValueEnv)
> initEnvs = (initPEnv,initTCEnv,initDCEnv)

\end{verbatim}
An implicit import of the prelude is added to the declarations of
every module, except for the prelude itself. If no explicit import for
the prelude is present, the prelude is imported unqualified, otherwise
only a qualified import is added.
\begin{verbatim}

> importPrelude :: FilePath -> Module -> Module
> importPrelude fn (Module m es ds) =
>   Module m es (if m == preludeMIdent then ds else ds')
>   where ids = filter isImportDecl ds
>         ds' = ImportDecl (first fn) preludeMIdent
>                          (preludeMIdent `elem` map importedModule ids)
>                          Nothing Nothing : ds
>         importedModule (ImportDecl _ m q asM is) = fromMaybe m asM

\end{verbatim}
If an import declaration for a module is found, the compiler first
checks whether an import for the module is already pending. In this
case the module imports are cyclic which is not allowed in Curry. The
compilation will therefore be aborted. Next, the compiler checks
whether the module has been imported already. If so, nothing needs to
be done, otherwise the interface will be searched in the import paths
and compiled.
\begin{verbatim}

> loadInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv ->
>     (Position,ModuleIdent) -> IO ModuleEnv
> loadInterface paths ctxt mEnv (p,m)
>   | m `elem` ctxt = errorAt p (cyclicImport m (takeWhile (/= m) ctxt))
>   | isLoaded m mEnv = return mEnv
>   | otherwise =
>       lookupInterface paths m >>=
>       maybe (errorAt p (interfaceNotFound m))
>             (compileInterface paths ctxt mEnv m)
>   where isLoaded m mEnv = maybe False (const True) (lookupModule m mEnv)

\end{verbatim}
After parsing an interface, all imported interfaces are recursively
loaded and entered into the interface's environment.
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> ModuleIdent
>                  -> FilePath -> IO ModuleEnv
> compileInterface paths ctxt mEnv m fn =
>   do
>     intf@(Interface m' _) <- liftM (ok . parseInterface fn) (readFile fn)
>     unless (m == m') (errorAt (first fn) (wrongInterface m m'))
>     mEnv' <- loadIntfInterfaces paths ctxt mEnv intf
>     return (bindModule (checkInterface mEnv' intf) mEnv')

> loadIntfInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> Interface
>                    -> IO ModuleEnv
> loadIntfInterfaces paths ctxt mEnv (Interface m ds) =
>   foldM (loadInterface paths (m:ctxt)) mEnv [(p,m) | IImportDecl p m <- ds]

> checkInterface :: ModuleEnv -> Interface -> Interface
> checkInterface mEnv (Interface m ds) =
>   intfCheck pEnv tcEnv tyEnv (Interface m ds)
>   where (pEnv,tcEnv,tyEnv) = foldl importInterface initEnvs ds
>         importInterface (pEnv,tcEnv,tyEnv) (IImportDecl p m) =
>           case lookupModule m mEnv of
>             Just ds -> importInterfaceIntf (Interface m ds) pEnv tcEnv tyEnv
>             Nothing -> internalError "importInterface"
>         importInterface (pEnv,tcEnv,tyEnv) _ = (pEnv,tcEnv,tyEnv)

\end{verbatim}
After checking the module successfully, the compiler may need to
update the module's interface file. The file will be updated only if
the interface has been changed or the file did not exist before.

The code is a little bit tricky because we must make sure that the
interface file is closed before rewriting the interface, even if it
has not been read completely. On the other hand, we must not apply
\texttt{hClose} too early. Note that there is no need to close the
interface explicitly if the interface check succeeds because the whole
file must have been read in this case. In addition, we do not update
the interface file in this case and therefore it doesn't matter when
the file is closed.
\begin{verbatim}

> updateInterface :: FilePath -> Interface -> IO ()
> updateInterface sfn i =
>   do
>     eq <- catch (matchInterface ifn i) (const (return False))
>     unless eq (writeInterface ifn i)
>   where ifn = rootname sfn ++ intfExt

> matchInterface :: FilePath -> Interface -> IO Bool
> matchInterface ifn i =
>   do
>     h <- openFile ifn ReadMode
>     s <- hGetContents h
>     case parseInterface ifn s of
>       Ok i' | i `intfEquiv` fixInterface i' -> return True
>       _ -> hClose h >> return False

> writeInterface :: FilePath -> Interface -> IO ()
> writeInterface ifn = writeFile ifn . showln . ppInterface

\end{verbatim}
The compiler searches for interface files in the import search path
using the extension \texttt{".icurry"}. Note that the current
directory is always searched first.
\begin{verbatim}

> lookupInterface :: [FilePath] -> ModuleIdent -> IO (Maybe FilePath)
> lookupInterface paths m = lookupFile (ifn : [catPath p ifn | p <- paths])
>   where ifn = foldr1 catPath (moduleQualifiers m) ++ intfExt

\end{verbatim}
Literate source files use the extension \texttt{".lcurry"}.
\begin{verbatim}

> unlitLiterate :: FilePath -> String -> String
> unlitLiterate fn s
>   | not (isLiterateSource fn) = s
>   | null es = s'
>   | otherwise = error es
>   where (es,s') = unlit fn s

> isLiterateSource :: FilePath -> Bool
> isLiterateSource fn = litExt `isSuffixOf` fn

\end{verbatim}
The \texttt{doDump} function writes the selected information to the
standard output.
\begin{verbatim}

> doDump :: Options -> (Dump,Doc) -> IO ()
> doDump opts (d,x) =
>   when (d `elem` dump opts)
>        (print (text hd $$ text (replicate (length hd) '=') $$ x))
>   where hd = dumpHeader d

> dumpHeader :: Dump -> String
> dumpHeader DumpRenamed = "Module after renaming"
> dumpHeader DumpTypes = "Types"
> dumpHeader DumpDesugared = "Source code after desugaring"
> dumpHeader DumpSimplified = "Source code after simplification"
> dumpHeader DumpLifted = "Source code after lifting"
> dumpHeader DumpIL = "Intermediate code"
> dumpHeader DumpTransformed = "Transformed code" 
> dumpHeader DumpNormalized = "Intermediate code after normalization"
> dumpHeader DumpCam = "Abstract machine code"


\end{verbatim}
The function \testtt{genCurry} generates several kinds of abstract
curry representations (FlatCurry, AbstractCurry and FlatXML)
depending on the specified option.
\begin{verbatim}

> genCurry :: Options -> FilePath -> ModuleEnv -> Module -> IL.Module -> IO ()
> genCurry opts fname mEnv mod il
>   | flat      = writeFlat fname' fname info il
>   | abstract  = error "AbstractCurry program generation not supported" 
>   | xml       = writeXML fname' fname info il 
>   | otherwise = error "Illegal option"
>  where
>  fname'   = output opts
>  info     = genCurryInfo mEnv mod
>  flat     = flatCurry opts
>  abstract = abstractCurry opts
>  xml      = flatXML opts


\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: ModuleIdent -> [(Ident,ValueInfo)] -> Doc
> ppTypes m = vcat . map (ppIDecl . mkDecl) . filter (isValue . snd)
>   where mkDecl (v,Value _ (ForAll _ ty)) =
>           IFunctionDecl undefined (qualify v) (fromQualType m ty)
>         isValue (DataConstructor _ _) = False
>         isValue (NewtypeConstructor _ _) = False
>         isValue (Value _ _) = True

\end{verbatim}
Various filename extensions
\begin{verbatim}

> cExt = ".c"
> xmlExt = "_flat.xml"
> flatExt = ".fcy"
> flatIntExt = ".fint"
> acyExt = ".acy"
> intfExt = ".icurry"
> litExt = ".lcurry"

\end{verbatim}
Error functions.
\begin{verbatim}

> interfaceNotFound :: ModuleIdent -> String
> interfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

> cyclicImport :: ModuleIdent -> [ModuleIdent] -> String
> cyclicImport m [] = "Recursive import for module " ++ moduleName m
> cyclicImport m ms =
>   "Cyclic import dependency between modules " ++ moduleName m ++
>     modules "" ms
>   where modules comma [m] = comma ++ " and " ++ moduleName m
>         modules _ (m:ms) = ", " ++ moduleName m ++ modules "," ms

> wrongInterface :: ModuleIdent -> ModuleIdent -> String
> wrongInterface m m' =
>   "Expected interface for " ++ show m ++ " but found " ++ show m'

\end{verbatim}
