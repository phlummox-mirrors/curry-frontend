
% $Id: Modules.lhs,v 1.84 2004/02/10 17:46:07 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% March 2007, extensions by Sebastian Fischer (sebf@informatik.uni-kiel.de)
%
\nwfilename{Modules.lhs}
\section{Modules}
This module controls the compilation of modules.

Since this version is only used as a frontend for PAKCS, some of the following 
import declarations are commented out
\begin{verbatim}

> module Modules(compileModule,
>                importPrelude, patchModuleId,
>	         loadInterfaces, transModule,
>	         simpleCheckModule, checkModule
>	        ) where


> import Data.List
> import qualified Data.Map as Map
> import System.IO
> import Data.Maybe
> import Control.Monad

> import Curry.Base.MessageMonad
> import Curry.Base.Position
> import Curry.Base.Ident
> import Curry.Syntax
> import Curry.Syntax.Pretty(ppModule,ppIDecl)
> import Curry.Syntax.ShowModule(showModule)

> import Base
> import Types
> import KindCheck(kindCheck)
> import SyntaxCheck(syntaxCheck)
> import PrecCheck(precCheck)
> import TypeCheck(typeCheck)
> import WarnCheck(warnCheck)
> import Arity
> import Imports(importInterface,importInterfaceIntf,importUnifyData)
> import Exports(expandInterface,exportInterface)
> import Eval(evalEnv)
> import Qual(qual)
> import Desugar(desugar)
> import Simplify(simplify)
> import Lift(lift)
> import qualified IL.Type as IL
> import IL.CurryToIL(ilTrans)
> import IL.XML(xmlModule)
> import Curry.ExtendedFlat
> import GenFlatCurry (genFlatCurry,genFlatInterface)
> import Curry.AbstractCurry
> import GenAbstractCurry
> import InterfaceCheck
> import CurryEnv
> import qualified IL.Pretty(ppModule)
> import CurryCompilerOpts(Options(..),Dump(..))
> import CaseCompletion
> import PathUtils
> import Filenames
> import TypeSubst
> import PrettyCombinators
> import TopEnv

\end{verbatim}
The function \texttt{compileModule} is the main entry-point of this
module for compiling a Curry source module. Depending on the command
line options it will emit either C code or FlatCurry code (standard 
or in XML
representation) or AbtractCurry code (typed, untyped or with type
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

> compileModule :: Options -> FilePath -> IO (Maybe FilePath)
> compileModule opts fn =
>   do
>     mod <- liftM (importPrelude fn . ok . parseModule likeFlat fn) (readModule fn)
>     let m = patchModuleId fn mod
>     checkModuleId fn m
>     mEnv <- loadInterfaces (importPaths opts) m
>     if uacy || src
>        then 
>          do (tyEnv, tcEnv, aEnv, m', intf, _) <- simpleCheckModule opts mEnv m
>             if uacy then genAbstract opts fn tyEnv tcEnv m'
>                     else do
>                       let outputFile = maybe (sourceRepName fn)
>                                              id 
>                                              (output opts)
>                           outputMod = showModule m'
>                       writeModule outputFile outputMod
>                       return Nothing
>        else
>          do (tyEnv, tcEnv, aEnv, m', intf, _) <- checkModule opts mEnv m
>             let (il,aEnv',dumps) = transModule fcy False False 
>			                         mEnv tyEnv tcEnv aEnv m'
>             mapM_ (doDump opts) dumps
>	      genCode opts fn mEnv tyEnv tcEnv aEnv' intf m' il
>   where acy      = abstract opts
>         uacy     = untypedAbstract opts
>         fcy      = flat opts
>         xml      = flatXml opts
>         src      = parseOnly opts
>         likeFlat = fcy || xml || acy || uacy || src
>	  
>         genCode opts fn mEnv tyEnv tcEnv aEnv intf m il
>            | fcy || xml = genFlat opts fn mEnv tyEnv tcEnv aEnv intf m il
>            | acy        = genAbstract opts fn tyEnv tcEnv m
>            | otherwise  = return Nothing

> loadInterfaces :: [FilePath] -> Module -> IO ModuleEnv
> loadInterfaces paths (Module m _ ds) =
>   foldM (loadInterface paths [m]) Map.empty
>         [(p,m) | ImportDecl p m _ _ _ <- ds]

> checkModuleId :: Monad m => FilePath -> Module -> m ()
> checkModuleId fn (Module mid _ _)
>    | last (moduleQualifiers mid) == takeBaseName fn
>      = return ()
>    | otherwise
>      = error ("module \"" ++ moduleName mid 
>	        ++ "\" must be in a file \"" ++ moduleName mid
>	        ++ ".curry\"")

> simpleCheckModule :: Options -> ModuleEnv -> Module 
>	    -> IO (ValueEnv,TCEnv,ArityEnv,Module,Interface,[WarnMsg])
> simpleCheckModule opts mEnv (Module m es ds) =
>   do unless (noWarn opts) (printMessages msgs)
>      return (tyEnv'', tcEnv, aEnv'', modul, intf, msgs)
>   where (impDs,topDs) = partition isImportDecl ds
>         iEnv = foldr bindAlias initIEnv impDs
>         (pEnv,tcEnv,tyEnv,aEnv) = importModules mEnv impDs
>         msgs = warnCheck m tyEnv impDs topDs
>	  withExt = withExtensions opts
>         (pEnv',topDs') = precCheck m pEnv 
>		           $ syntaxCheck withExt m iEnv aEnv tyEnv tcEnv
>			   $ kindCheck m tcEnv topDs
>         ds' = impDs ++ qual m tyEnv topDs'
>         modul = (Module m es ds') --expandInterface (Module m es ds') tcEnv tyEnv
>         (_,tcEnv'',tyEnv'',aEnv'') 
>            = qualifyEnv mEnv pEnv' tcEnv tyEnv aEnv
>         intf = exportInterface modul pEnv' tcEnv'' tyEnv''

> checkModule :: Options -> ModuleEnv -> Module 
>      -> IO (ValueEnv,TCEnv,ArityEnv,Module,Interface,[WarnMsg])
> checkModule opts mEnv (Module m es ds) =
>   do unless (noWarn opts) (printMessages msgs)
>      when (m == mkMIdent ["field114..."])
>           (error (show es))
>      return (tyEnv''', tcEnv', aEnv'', modul, intf, msgs)
>   where (impDs,topDs) = partition isImportDecl ds
>         iEnv = foldr bindAlias initIEnv impDs
>         (pEnv,tcEnvI,tyEnvI,aEnv) = importModules mEnv impDs
>         tcEnv = if withExtensions opts
>	             then fmap (expandRecordTC tcEnvI) tcEnvI
>		     else tcEnvI
>         lEnv = importLabels mEnv impDs
>	  tyEnvL = addImportedLabels m lEnv tyEnvI
>	  tyEnv = if withExtensions opts
>	             then fmap (expandRecordTypes tcEnv) tyEnvL
>		     else tyEnvI
>         msgs = warnCheck m tyEnv impDs topDs
>	  withExt = withExtensions opts
>         (pEnv',topDs') = precCheck m pEnv 
>		           $ syntaxCheck withExt m iEnv aEnv tyEnv tcEnv
>			   $ kindCheck m tcEnv topDs
>         (tcEnv',tyEnv') = typeCheck m tcEnv tyEnv topDs'
>         ds' = impDs ++ qual m tyEnv' topDs'
>         modul = expandInterface (Module m es ds') tcEnv' tyEnv'
>         (pEnv'',tcEnv'',tyEnv'',aEnv'') 
>            = qualifyEnv mEnv pEnv' tcEnv' tyEnv' aEnv
>         tyEnvL' = addImportedLabels m lEnv tyEnv''
>	  tyEnv''' = if withExtensions opts
>	                then fmap (expandRecordTypes tcEnv'') tyEnvL'
>		        else tyEnv''
>         --tyEnv''' = addImportedLabels m lEnv tyEnv''
>         intf = exportInterface modul pEnv'' tcEnv'' tyEnv'''

> transModule :: Bool -> Bool -> Bool -> ModuleEnv -> ValueEnv -> TCEnv
>      -> ArityEnv -> Module -> (IL.Module,ArityEnv,[(Dump,Doc)])
> transModule flat debug trusted mEnv tyEnv tcEnv aEnv (Module m es ds) =
>     (il',aEnv',dumps)
>   where topDs = filter (not . isImportDecl) ds
>         evEnv = evalEnv topDs
>         (desugared,tyEnv') = desugar tyEnv tcEnv (Module m es topDs)
>         (simplified,tyEnv'') = simplify flat tyEnv' evEnv desugared
>         (lifted,tyEnv''',evEnv') = lift tyEnv'' evEnv simplified
>         aEnv' = bindArities aEnv lifted
>         il = ilTrans flat tyEnv''' tcEnv evEnv' lifted
>         il' = completeCase mEnv il
>         dumps = [(DumpRenamed,ppModule (Module m es ds)),
>	           (DumpTypes,ppTypes m (localBindings tyEnv)),
>	           (DumpDesugared,ppModule desugared),
>                  (DumpSimplified,ppModule simplified),
>                  (DumpLifted,ppModule lifted),
>                  (DumpIL,IL.Pretty.ppModule il),
>	           (DumpCase,IL.Pretty.ppModule il')
>	          ]

> qualifyEnv :: ModuleEnv -> PEnv -> TCEnv -> ValueEnv -> ArityEnv
>     -> (PEnv,TCEnv,ValueEnv,ArityEnv)
> qualifyEnv mEnv pEnv tcEnv tyEnv aEnv =
>   (foldr bindQual pEnv' (localBindings pEnv),
>    foldr bindQual tcEnv' (localBindings tcEnv),
>    foldr bindGlobal tyEnv' (localBindings tyEnv),
>    foldr bindQual aEnv' (localBindings aEnv))
>   where (pEnv',tcEnv',tyEnv',aEnv') =
>           foldl importInterface initEnvs (Map.toList mEnv)
>         importInterface (pEnv,tcEnv,tyEnv,aEnv) (m,ds) =
>           importInterfaceIntf (Interface m ds) pEnv tcEnv tyEnv aEnv
>         bindQual (_,y) = qualBindTopEnv "Modules.qualifyEnv" (origName y) y
>         bindGlobal (x,y)
>           | uniqueId x == 0 = bindQual (x,y)
>           | otherwise = bindTopEnv "Modules.qualifyEnv" x y

> writeXML :: Maybe FilePath -> FilePath -> CurryEnv -> IL.Module -> IO ()
> writeXML tfn sfn cEnv il = writeModule ofn (showln code)
>   where ofn  = fromMaybe (xmlName sfn) tfn
>         code = (xmlModule cEnv il)

> writeFlat :: Options -> Maybe FilePath -> FilePath -> CurryEnv -> ModuleEnv 
>              -> ValueEnv -> TCEnv -> ArityEnv -> IL.Module -> IO Prog
> writeFlat opts tfn sfn cEnv mEnv tyEnv tcEnv aEnv il
>   = writeFlatFile opts (genFlatCurry opts cEnv mEnv tyEnv tcEnv aEnv il)
>                        (fromMaybe (flatName sfn) tfn)

> writeFlatFile :: Options -> (Prog, [WarnMsg]) -> String -> IO Prog
> writeFlatFile opts@Options{extendedFlat=ext} (res,msgs) fname = do
>         unless (noWarn opts) (printMessages msgs)
>	  if ext then writeExtendedFlat fname res
>                else writeFlatCurry fname res
>         return res


> writeTypedAbs :: Maybe FilePath -> FilePath -> ValueEnv -> TCEnv -> Module
>	           -> IO ()
> writeTypedAbs tfn sfn tyEnv tcEnv mod
>    = writeCurry fname (genTypedAbstract tyEnv tcEnv mod)
>  where fname = fromMaybe (acyName sfn) tfn

> writeUntypedAbs :: Maybe FilePath -> FilePath -> ValueEnv -> TCEnv  
>	             -> Module -> IO ()
> writeUntypedAbs tfn sfn tyEnv tcEnv mod
>    = writeCurry fname (genUntypedAbstract tyEnv tcEnv mod)
>  where fname = fromMaybe (uacyName sfn) tfn

> showln :: Show a => a -> String
> showln x = shows x "\n"

\end{verbatim}

The function \texttt{importModules} brings the declarations of all
imported modules into scope for the current module.
\begin{verbatim}

> importModules :: ModuleEnv -> [Decl] -> (PEnv,TCEnv,ValueEnv,ArityEnv)
> importModules mEnv ds = (pEnv,importUnifyData tcEnv,tyEnv,aEnv)
>   where (pEnv,tcEnv,tyEnv,aEnv) = foldl importModule initEnvs ds
>         importModule (pEnv,tcEnv,tyEnv,aEnv) (ImportDecl p m q asM is) =
>           case lookupModule m mEnv of
>             Just ds -> importInterface p (fromMaybe m asM) q is
>                                        (Interface m ds) pEnv tcEnv tyEnv aEnv
>             Nothing -> internalError "importModule"
>         importModule (pEnv,tcEnv,tyEnv,aEnv) _ = (pEnv,tcEnv,tyEnv,aEnv)

> initEnvs :: (PEnv,TCEnv,ValueEnv,ArityEnv)
> initEnvs = (initPEnv,initTCEnv,initDCEnv,initAEnv)

\end{verbatim}
Unlike unsual identifiers like in functions, types etc. identifiers
of labels are always represented unqualified within the whole context
of compilation. Since the common type environment (type \texttt{ValueEnv})
has some problems with handling imported unqualified identifiers, it is 
necessary to add the type information for labels seperately. For this reason
the function \texttt{importLabels} generates an environment containing
all imported labels and the function \texttt{addImportedLabels} adds this
content to a type environment.
\begin{verbatim}

> importLabels :: ModuleEnv -> [Decl] -> LabelEnv
> importLabels mEnv ds = foldl importLabelTypes initLabelEnv ds
>   where
>   importLabelTypes lEnv (ImportDecl p m _ asM is) =
>     case (lookupModule m mEnv) of
>       Just ds' -> foldl (importLabelType p (fromMaybe m asM) is) lEnv ds'
>       Nothing -> internalError "importLabels"
>   importLabelTypes lEnv _ = lEnv
>		      
>   importLabelType p m is lEnv (ITypeDecl _ r _ (RecordType fs _)) =
>     foldl (insertLabelType p m r' (getImportSpec r' is)) lEnv fs
>     where r' = qualifyWith m (fromRecordExtId (unqualify r))
>   importLabelType _ _ _ lEnv _ = lEnv
>			   
>   insertLabelType p m r (Just (ImportTypeAll _)) lEnv ([l],ty) =
>     bindLabelType l r (toType [] ty) lEnv
>   insertLabelType p m r (Just (ImportTypeWith _ ls)) lEnv ([l],ty)
>     | l `elem` ls = bindLabelType l r (toType [] ty) lEnv
>     | otherwise   = lEnv
>   insertLabelType _ _ _ _ lEnv _ = lEnv
>			     
>   getImportSpec r (Just (Importing _ is')) =
>     find (isImported (unqualify r)) is'
>   getImportSpec r Nothing = Just (ImportTypeAll (unqualify r))
>   getImportSpec r _ = Nothing
>		
>   isImported r (Import r') = r == r'
>   isImported r (ImportTypeWith r' _) = r == r'
>   isImported r (ImportTypeAll r') = r == r'

> addImportedLabels :: ModuleIdent -> LabelEnv -> ValueEnv -> ValueEnv
> addImportedLabels m lEnv tyEnv = 
>   foldr addLabelType tyEnv (concatMap snd (Map.toList lEnv))
>   where
>   addLabelType (LabelType l r ty) tyEnv = 
>     let m' = fromMaybe m (fst (splitQualIdent r))
>     in  importTopEnv m' l 
>                      (Label (qualify l) (qualQualify m' r) (polyType ty)) 
>	               tyEnv

\end{verbatim}
Fully expand all (imported) record types within the type constructor 
environment and the type environment.
Note: the record types for the current module are expanded within the
type check.
\begin{verbatim}

> expandRecordTC :: TCEnv -> TypeInfo -> TypeInfo
> expandRecordTC tcEnv (DataType qid n args) =
>   DataType qid n (map (maybe Nothing (Just . (expandData tcEnv))) args)
> expandRecordTC tcEnv (RenamingType qid n (Data id m ty)) =
>   RenamingType qid n (Data id m (expandRecords tcEnv ty))
> expandRecordTC tcEnv (AliasType qid n ty) =
>   AliasType qid n (expandRecords tcEnv ty)

> expandData :: TCEnv -> Data [Type] -> Data [Type]
> expandData tcEnv (Data id n tys) =
>   Data id n (map (expandRecords tcEnv) tys)

> expandRecordTypes :: TCEnv -> ValueInfo -> ValueInfo
> expandRecordTypes tcEnv (DataConstructor qid (ForAllExist n m ty)) =
>   DataConstructor qid (ForAllExist n m (expandRecords tcEnv ty))
> expandRecordTypes tcEnv (NewtypeConstructor qid (ForAllExist n m ty)) =
>   NewtypeConstructor qid (ForAllExist n m (expandRecords tcEnv ty))
> expandRecordTypes tcEnv (Value qid (ForAll n ty)) =
>   Value qid (ForAll n (expandRecords tcEnv ty))
> expandRecordTypes tcEnv (Label qid r (ForAll n ty)) =
>   Label qid r (ForAll n (expandRecords tcEnv ty))

> expandRecords :: TCEnv -> Type -> Type
> expandRecords tcEnv (TypeConstructor qid tys) =
>   case (qualLookupTC qid tcEnv) of
>     [AliasType _ _ rty@(TypeRecord _ _)]
>       -> expandRecords tcEnv 
>            (expandAliasType (map (expandRecords tcEnv) tys) rty)
>     _ -> TypeConstructor qid (map (expandRecords tcEnv) tys)
> expandRecords tcEnv (TypeConstrained tys v) =
>   TypeConstrained (map (expandRecords tcEnv) tys) v
> expandRecords tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (expandRecords tcEnv ty1) (expandRecords tcEnv ty2)
> expandRecords tcEnv (TypeRecord fs rv) =
>   TypeRecord (map (\ (l,ty) -> (l,expandRecords tcEnv ty)) fs) rv
> expandRecords _ ty = ty

\end{verbatim}
An implicit import of the prelude is added to the declarations of
every module, except for the prelude itself. If no explicit import for
the prelude is present, the prelude is imported unqualified, otherwise
only a qualified import is added.
\begin{verbatim}

> importPrelude :: FilePath -> Module -> Module
> importPrelude fn (Module m es ds) =
>   Module m es (if m == preludeMIdent then ds else ds')
>   where ids = [decl | decl@(ImportDecl _ _ _ _ _) <- ds]
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
After reading an interface, all imported interfaces are recursively
loaded and entered into the interface's environment. There is no need
to check FlatCurry-Interfaces, since these files contain automaticaly
generated FlatCurry terms (type \texttt{Prog}).
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> ModuleIdent
>                  -> FilePath -> IO ModuleEnv
> compileInterface paths ctxt mEnv m fn =
>   do
>     mintf <- readFlatInterface fn
>     let intf = fromMaybe (errorAt (first fn) (interfaceNotFound m)) mintf
>         (Prog mod _ _ _ _) = intf
>         m' = mkMIdent [mod]
>     unless (m' == m) (errorAt (first fn) (wrongInterface m m'))
>     mEnv' <- loadFlatInterfaces paths ctxt mEnv intf
>     return (bindFlatInterface intf mEnv')

> --loadIntfInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> Interface
> --                   -> IO ModuleEnv
> --loadIntfInterfaces paths ctxt mEnv (Interface m ds) =
> --  foldM (loadInterface paths (m:ctxt)) mEnv [(p,m) | IImportDecl p m <- ds]


> loadFlatInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> Prog
>                    -> IO ModuleEnv
> loadFlatInterfaces paths ctxt mEnv (Prog m is _ _ _) =
>   foldM (loadInterface paths ((mkMIdent [m]):ctxt)) 
>         mEnv 
>         (map (\i -> (p, mkMIdent [i])) is)
>  where p = first m

> --checkInterface :: ModuleEnv -> Interface -> Interface
> --checkInterface mEnv (Interface m ds) =
> --  intfCheck pEnv tcEnv tyEnv (Interface m ds)
> --  where (pEnv,tcEnv,tyEnv) = foldl importInterface initEnvs ds
> --        importInterface (pEnv,tcEnv,tyEnv) (IImportDecl p m) =
> --          case lookupModule m mEnv of
> --            Just ds -> importInterfaceIntf (Interface m ds) pEnv tcEnv tyEnv
> --            Nothing -> internalError "importInterface"
> --        importInterface (pEnv,tcEnv,tyEnv) _ = (pEnv,tcEnv,tyEnv)


\end{verbatim}
Interface files are updated by the Curry builder when necessary.
(see module \texttt{CurryBuilder}).

Description of the following obsolete functions:
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

> --updateInterface :: FilePath -> Interface -> IO ()
> --updateInterface sfn i =
> --  do
> --    eq <- catch (matchInterface ifn i) (const (return False))
> --    unless eq (writeInterface ifn i)
> --  where ifn = dropExtension sfn ++ intfExt

> --matchInterface :: FilePath -> Interface -> IO Bool
> --matchInterface ifn i =
> --  do
> --    h <- openFile ifn ReadMode
> --    s <- hGetContents h
> --    case parseInterface ifn s of
> --      Ok i' | i `intfEquiv` fixInterface i' -> return True
> --      _ -> hClose h >> return False

> --writeInterface :: FilePath -> Interface -> IO ()
> --writeInterface ifn = writeFile ifn . showln . ppInterface

\end{verbatim}
The compiler searches for interface files in the import search path
using the extension \texttt{".fint"}. Note that the current
directory is always searched first.
\begin{verbatim}

> lookupInterface :: [FilePath] -> ModuleIdent -> IO (Maybe FilePath)
> lookupInterface paths m = lookupFile ("":paths) [flatIntExt] ifn
>   where ifn = foldr1 catPath (moduleQualifiers m)

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
> dumpHeader DumpCase = "Intermediate code after case simplification"
> --dumpHeader DumpTransformed = "Transformed code" 
> --dumpHeader DumpNormalized = "Intermediate code after normalization"
> --dumpHeader DumpCam = "Abstract machine code"


\end{verbatim}
The functions \texttt{genFlat} and \texttt{genAbstract} generate
flat and abstract curry representations depending on the specified option.
If the interface of a modified Curry module did not change, the corresponding 
file name will be returned within the result of \texttt{genFlat} (depending
on the compiler flag "force") and other modules importing this module won't
be dependent on it any longer.
\begin{verbatim}

> genFlat :: Options -> FilePath -> ModuleEnv -> ValueEnv -> TCEnv -> ArityEnv 
>            -> Interface -> Module -> IL.Module -> IO (Maybe FilePath)
> genFlat opts fname mEnv tyEnv tcEnv aEnv intf mod il
>   | flat opts
>     = do writeFlat opts Nothing fname cEnv mEnv tyEnv tcEnv aEnv il
>          let (flatInterface,intMsgs) = genFlatInterface opts cEnv mEnv tyEnv tcEnv aEnv il
>          if force opts
>            then 
>              do writeInterface flatInterface intMsgs
>                 return Nothing
>            else 
>               do mfint <- readFlatInterface fintName
>                  let flatIntf = fromMaybe emptyIntf mfint
>                  if mfint == mfint  -- necessary to close the file 'fintName'
>                        && not (interfaceCheck flatIntf flatInterface)
>                     then 
>                        do writeInterface flatInterface intMsgs
>                           return Nothing
>                     else return Nothing
>   | flatXml opts
>     = writeXML (output opts) fname cEnv il >> return Nothing
>   | otherwise
>     = internalError "@Modules.genFlat: illegal option"
>  where
>    fintName = flatIntName fname
>    cEnv = curryEnv mEnv tcEnv intf mod
>    emptyIntf = Prog "" [] [] [] []
>    writeInterface intf msgs = do
>          unless (noWarn opts) (printMessages msgs)
>          writeFlatCurry fintName intf


> genAbstract :: Options -> FilePath  -> ValueEnv -> TCEnv -> Module 
>                -> IO (Maybe FilePath)
> genAbstract opts fname tyEnv tcEnv mod
>    | abstract opts
>      = do writeTypedAbs Nothing fname tyEnv tcEnv mod 
>           return Nothing
>    | untypedAbstract opts
>      = do writeUntypedAbs Nothing fname tyEnv tcEnv mod
>           return Nothing
>    | otherwise
>      = internalError "@Modules.genAbstract: illegal option"

> printMessages :: [WarnMsg] -> IO ()
> printMessages []   = return ()
> printMessages msgs = hPutStrLn stderr $ unlines $ map showWarning msgs

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: ModuleIdent -> [(Ident,ValueInfo)] -> Doc
> ppTypes m = vcat . map (ppIDecl . mkDecl) . filter (isValue . snd)
>   where mkDecl (v,Value _ (ForAll _ ty)) =
>           IFunctionDecl undefined (qualify v) (arrowArity ty) 
>		      (fromQualType m ty)
>         isValue (DataConstructor _ _) = False
>         isValue (NewtypeConstructor _ _) = False
>         isValue (Value _ _) = True
>         isValue (Label _ _ _) = False


\end{verbatim}
A module which doesn't contain a \texttt{module ... where} declaration
obtains its filename as module identifier (unlike the definition in
Haskell and original MCC where a module obtains \texttt{main}).
\begin{verbatim}

> patchModuleId :: FilePath -> Module -> Module
> patchModuleId fn (Module mid mexports decls)
>    | (moduleName mid) == "main"
>      = Module (mkMIdent [takeBaseName fn]) mexports decls
>    | otherwise
>      = Module mid mexports decls


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
