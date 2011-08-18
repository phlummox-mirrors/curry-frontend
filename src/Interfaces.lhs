\paragraph{Interfaces}
The compiler maintains a global environment holding all (directly or
indirectly) imported interface declarations.

Interface files are updated by the Curry builder when necessary.
(see module \texttt{CurryBuilder}).
\begin{verbatim}

> module Interfaces (loadInterfaces) where

> import Control.Monad (foldM, liftM, unless)
> import Data.List (isPrefixOf)
> import qualified Data.Map as Map

> import Curry.Base.Ident
> import Curry.Base.Position
> import qualified Curry.ExtendedFlat.Type as EF
> import Curry.Files.PathUtils as PU
> import Curry.Syntax

> import Base.ErrorMessages (errCyclicImport, errInterfaceNotFound
>   , errWrongInterface)
> import Base.Messages (errorAt)

> import Env.Interfaces

> -- |Load the interface files into the 'InterfaceEnv'
> loadInterfaces :: [FilePath] -> Module -> IO InterfaceEnv
> loadInterfaces paths (Module m _ ds) =
>   foldM (loadInterface paths [m]) initInterfaceEnv
>         [(p, m') | ImportDecl p m' _ _ _ <- ds]

\end{verbatim}
If an import declaration for a module is found, the compiler first
checks whether an import for the module is already pending. In this
case the module imports are cyclic which is not allowed in Curry. The
compilation will therefore be aborted. Next, the compiler checks
whether the module has already been imported. If so, nothing needs to
be done, otherwise the interface will be searched for in the import paths
and compiled.
\begin{verbatim}

> loadInterface :: [FilePath] -> [ModuleIdent] -> InterfaceEnv
>               -> (Position, ModuleIdent) -> IO InterfaceEnv
> loadInterface paths ctxt mEnv (p, m)
>   | m `elem` ctxt       = errorAt p
>                         $ errCyclicImport $ m : takeWhile (/= m) ctxt
>   | m `Map.member` mEnv = return mEnv
>   | otherwise           = PU.lookupInterface paths m >>=
>       maybe (errorAt p $ errInterfaceNotFound m)
>             (compileInterface paths ctxt mEnv m)

\end{verbatim}
After reading an interface, all imported interfaces are recursively
loaded and entered into the interface's environment. There is no need
to check FlatCurry-Interfaces, since these files contain automatically
generated FlatCurry terms (type \texttt{Prog}).
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> InterfaceEnv
>                  -> ModuleIdent -> FilePath -> IO InterfaceEnv
> compileInterface paths ctxt mEnv m fn = do
>   mintf <- (fmap flatToCurryInterface) `liftM` EF.readFlatInterface fn
>   case mintf of
>     Nothing                -> errorAt (first fn) $ errInterfaceNotFound m
>     Just (Interface m' ds) -> do
>       unless (m' == m) $ errorAt (first fn) $ errWrongInterface m m'
>       let importDecls = [ (pos, imp) | IImportDecl pos imp <- ds ]
>       mEnv' <- foldM (loadInterface paths (m : ctxt)) mEnv importDecls
>       return $ Map.insert m ds mEnv'

\end{verbatim}
The function \texttt{flatToCurryInterface} transforms FlatInterface
information (type \texttt{FlatCurry.Prog} to MCC interface declarations
(type \texttt{CurrySyntax.IDecl}. This is necessary to process
FlatInterfaces instead of ".icurry" files when using MCC as frontend
for PAKCS.
\begin{verbatim}

> flatToCurryInterface :: EF.Prog -> Interface
> flatToCurryInterface (EF.Prog m imps ts fs os)
>   = Interface (fromModuleName m) $ concat
>     [ map genIImportDecl imps
>     , map genITypeDecl $ filter (not . isSpecialPreludeType) ts
>     , map genIFuncDecl fs
>     , map genIOpDecl os
>     ]
>   where
>   pos = first m
>
>   genIImportDecl :: String -> IDecl
>   genIImportDecl = IImportDecl pos . fromModuleName
>
>   genITypeDecl :: EF.TypeDecl -> IDecl
>   genITypeDecl (EF.Type qn _ is cs)
>     | recordExt `isPrefixOf` EF.localName qn
>     = ITypeDecl pos
>                 (genQualIdent qn)
>                 (map (genVarIndexIdent "a") is)
>                 (RecordType (map genLabeledType cs) Nothing)
>     | otherwise
>     = IDataDecl pos
>                 (genQualIdent qn)
>                 (map (genVarIndexIdent "a") is)
>                 (map (Just . genConstrDecl) cs)
>   genITypeDecl (EF.TypeSyn qn _ is t)
>     = ITypeDecl pos
>                 (genQualIdent qn)
>                 (map (genVarIndexIdent "a") is)
>                 (genTypeExpr t)
>
>   genLabeledType :: EF.ConsDecl -> ([Ident], TypeExpr)
>   genLabeledType (EF.Cons qn _ _ [t])
>     = ( [renameLabel $ fromLabelExtId $ mkIdent $ EF.localName qn]
>       , genTypeExpr t)
>   genLabeledType _ = error "Interfaces.genLabeledType: no pattern match"
>
>   genConstrDecl :: EF.ConsDecl -> ConstrDecl
>   genConstrDecl (EF.Cons qn _ _ ts1)
>     = ConstrDecl pos [] (mkIdent (EF.localName qn)) (map genTypeExpr ts1)
>
>   genIFuncDecl :: EF.FuncDecl -> IDecl
>   genIFuncDecl (EF.Func qn a _ t _)
>     = IFunctionDecl pos (genQualIdent qn) a (genTypeExpr t)
>
>   genIOpDecl :: EF.OpDecl -> IDecl
>   genIOpDecl (EF.Op qn f p) = IInfixDecl pos (genInfix f) p (genQualIdent qn)
>
>   genTypeExpr :: EF.TypeExpr -> TypeExpr
>   genTypeExpr (EF.TVar i)
>     = VariableType (genVarIndexIdent "a" i)
>   genTypeExpr (EF.FuncType t1 t2)
>     = ArrowType (genTypeExpr t1) (genTypeExpr t2)
>   genTypeExpr (EF.TCons qn ts1)
>     = ConstructorType (genQualIdent qn) (map genTypeExpr ts1)
>
>   genInfix :: EF.Fixity -> Infix
>   genInfix EF.InfixOp  = Infix
>   genInfix EF.InfixlOp = InfixL
>   genInfix EF.InfixrOp = InfixR
>
>   genQualIdent :: EF.QName -> QualIdent
>   genQualIdent EF.QName { EF.modName = modul, EF.localName = lname } =
>     qualifyWith (fromModuleName modul) (mkIdent lname)
>
>   genVarIndexIdent :: String -> Int -> Ident
>   genVarIndexIdent v i = mkIdent $ v ++ show i
>
>   isSpecialPreludeType :: EF.TypeDecl -> Bool
>   isSpecialPreludeType (EF.Type qn _ _ _)
>     = (lname == "[]" || lname == "()") && modul == "Prelude"
>       where EF.QName { EF.modName = modul, EF.localName = lname} = qn
>   isSpecialPreludeType _ = False

\end{verbatim}
