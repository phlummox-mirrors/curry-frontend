\paragraph{Interfaces}
The compiler maintains a global environment holding all (directly or
indirectly) imported interface declarations.

The function \texttt{bindFlatInterface} transforms FlatInterface
information (type \texttt{FlatCurry.Prog} to MCC interface declarations
(type \texttt{CurrySyntax.IDecl}. This is necessary to process
FlatInterfaces instead of ".icurry" files when using MCC as frontend
for PAKCS.
\begin{verbatim}

> module Interfaces (loadInterfaces) where

> import Control.Monad (foldM, unless)
> import Data.List (isPrefixOf)
> import qualified Data.Map as Map
> import Data.Maybe (fromMaybe)

> import Curry.Base.Ident
> import Curry.Base.Position
> import qualified Curry.ExtendedFlat.Type as EF
> import Curry.Files.PathUtils
> import Curry.Syntax

> import Base.Messages (errorAt)

> import Env.Module

\end{verbatim}
If an import declaration for a module is found, the compiler first
checks whether an import for the module is already pending. In this
case the module imports are cyclic which is not allowed in Curry. The
compilation will therefore be aborted. Next, the compiler checks
whether the module has already been imported. If so, nothing needs to
be done, otherwise the interface will be searched for in the import paths
and compiled.
\begin{verbatim}

> -- |Load the interface files into the 'ModuleEnv'
> loadInterfaces :: [FilePath] -> Module -> IO ModuleEnv
> loadInterfaces paths (Module m _ ds) =
>   foldM (loadInterface paths [m]) initMEnv
>         [(p, m') | ImportDecl p m' _ _ _ <- ds]

> loadInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv ->
>     (Position, ModuleIdent) -> IO ModuleEnv
> loadInterface paths ctxt mEnv (p, m)
>   | m `elem` ctxt       = errorAt p (cyclicImport m (takeWhile (/= m) ctxt))
>   | m `Map.member` mEnv = return mEnv
>   | otherwise           = lookupInterface paths m >>=
>       maybe (errorAt p (interfaceNotFound m))
>             (compileInterface paths ctxt mEnv m)

\end{verbatim}
After reading an interface, all imported interfaces are recursively
loaded and entered into the interface's environment. There is no need
to check FlatCurry-Interfaces, since these files contain automatically
generated FlatCurry terms (type \texttt{Prog}).
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> ModuleIdent
>                  -> FilePath -> IO ModuleEnv
> compileInterface paths ctxt mEnv m fn = do
>   mintf <- EF.readFlatInterface fn
>   let intf = fromMaybe (errorAt (first fn) (interfaceNotFound m)) mintf
>       (EF.Prog modul _ _ _ _) = intf
>       m' = fromModuleName modul
>   unless (m' == m) (errorAt (first fn) (wrongInterface m m'))
>   mEnv' <- loadFlatInterfaces paths ctxt mEnv intf
>   return $ bindFlatInterface intf mEnv'

> loadFlatInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> EF.Prog
>                    -> IO ModuleEnv
> loadFlatInterfaces paths ctxt mEnv (EF.Prog m is _ _ _) =
>   foldM (loadInterface paths (fromModuleName m : ctxt))
>         mEnv
>         (map (\i -> (first m, fromModuleName i)) is)

Interface files are updated by the Curry builder when necessary.
(see module \texttt{CurryBuilder}).

> bindFlatInterface :: EF.Prog -> ModuleEnv -> ModuleEnv
> bindFlatInterface (EF.Prog m imps ts fs os) = Map.insert (fromModuleName m)
>   $ concat [ map genIImportDecl imps
>            , map genITypeDecl ts'
>            , map genIFuncDecl fs
>            , map genIOpDecl os
>            ]
>  where
>  ts' = filter (not . isSpecialPreludeType) ts
>  pos = first m
>
>  genIImportDecl :: String -> IDecl
>  genIImportDecl = IImportDecl pos . fromModuleName
>
>  genITypeDecl :: EF.TypeDecl -> IDecl
>  genITypeDecl (EF.Type qn _ is cs)
>    | recordExt `isPrefixOf` EF.localName qn
>    = ITypeDecl pos
>                (genQualIdent qn)
>	             (map (genVarIndexIdent "a") is)
>	             (RecordType (map genLabeledType cs) Nothing)
>    | otherwise
>    = IDataDecl pos
>                (genQualIdent qn)
>                (map (genVarIndexIdent "a") is)
>                (map (Just . genConstrDecl) cs)
>  genITypeDecl (EF.TypeSyn qn _ is t)
>    = ITypeDecl pos
>                (genQualIdent qn)
>                (map (genVarIndexIdent "a") is)
>                (genTypeExpr t)
>
>  genIFuncDecl :: EF.FuncDecl -> IDecl
>  genIFuncDecl (EF.Func qn a _ t _)
>    = IFunctionDecl pos (genQualIdent qn) a (genTypeExpr t)
>
>  genIOpDecl :: EF.OpDecl -> IDecl
>  genIOpDecl (EF.Op qn f p) = IInfixDecl pos (genInfix f) p  (genQualIdent qn)
>
>  genConstrDecl :: EF.ConsDecl -> ConstrDecl
>  genConstrDecl (EF.Cons qn _ _ ts1)
>    = ConstrDecl pos [] (mkIdent (EF.localName qn)) (map genTypeExpr ts1)
>
>  genLabeledType :: EF.ConsDecl -> ([Ident], TypeExpr)
>  genLabeledType (EF.Cons qn _ _ [t])
>    = ([renameLabel (fromLabelExtId (mkIdent $ EF.localName qn))], genTypeExpr t)
>  genLabeledType _ = error "Modules.bindFlatInterface.genLabeledType: no pattern match"
>
>  genTypeExpr :: EF.TypeExpr -> TypeExpr
>  genTypeExpr (EF.TVar i)
>    = VariableType (genVarIndexIdent "a" i)
>  genTypeExpr (EF.FuncType t1 t2)
>    = ArrowType (genTypeExpr t1) (genTypeExpr t2)
>  genTypeExpr (EF.TCons qn ts1)
>    = ConstructorType (genQualIdent qn) (map genTypeExpr ts1)
>
>  genInfix :: EF.Fixity -> Infix
>  genInfix EF.InfixOp  = Infix
>  genInfix EF.InfixlOp = InfixL
>  genInfix EF.InfixrOp = InfixR
>
>  genQualIdent :: EF.QName -> QualIdent
>  genQualIdent EF.QName { EF.modName = modul, EF.localName = lname } =
>    qualifyWith (fromModuleName modul) (mkIdent lname)
>
>  genVarIndexIdent :: String -> Int -> Ident
>  genVarIndexIdent v i = mkIdent (v ++ show i)
>
>  isSpecialPreludeType :: EF.TypeDecl -> Bool
>  isSpecialPreludeType (EF.Type EF.QName { EF.modName = modul, EF.localName = lname} _ _ _)
>    = (lname == "[]" || lname == "()") && modul == "Prelude"
>  isSpecialPreludeType _ = False


\end{verbatim}
Error functions.
\begin{verbatim}

> interfaceNotFound :: ModuleIdent -> String
> interfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

> wrongInterface :: ModuleIdent -> ModuleIdent -> String
> wrongInterface m m' =
>   "Expected interface for " ++ show m ++ " but found " ++ show m'
>   ++ show (moduleQualifiers m, moduleQualifiers m')

> cyclicImport :: ModuleIdent -> [ModuleIdent] -> String
> cyclicImport m [] = "Recursive import for module " ++ moduleName m
> cyclicImport m ms =
>   "Cyclic import dependency between modules " ++ moduleName m ++
>     modules "" ms
>   where modules comm [m1] = comm ++ " and " ++ moduleName m1
>         modules _ (m1:ms1) = ", " ++ moduleName m1 ++ modules "," ms1
>         modules _ [] = error "Modules.cyclicImport.modules: empty list"

\end{verbatim}
