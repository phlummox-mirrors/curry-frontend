> {- |
>     Module      :  $Header$
>     Description :  Cumputation of export interface
>     Copyright   :  (c) 2000-2004, Wolfgang Lux
>                        2005, Martin Engelke (men@informatik.uni-kiel.de)
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

\nwfilename{Exports.lhs}
\section{Creating Interfaces}
This section describes how the exported interface of a compiled module
is computed.
\begin{verbatim}

> module Exports (expandInterface, exportInterface) where

> import Data.List
> import qualified Data.Map as Map
> import Data.Maybe
> import qualified Data.Set as Set

> import Curry.Base.Position
> import Curry.Base.Ident
> import Curry.Syntax

> import Base.CurryTypes (fromQualType)
> import Base.Messages
> import Base.TopEnv
> import Base.Types
> import Base.Utils (findDouble)

> import Env.OpPrec (PEnv, PrecInfo (..), OpPrec (..), qualLookupP)
> import Env.TypeConstructors (TCEnv, TypeInfo (..), qualLookupTC)
> import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

> import CompilerEnv

\end{verbatim}
The interface of a module is computed in two steps. The function
\texttt{expandInterface} checks the export specifications of the
module and expands them into a list containing all exported types and
functions, combining multiple exports for the same entity. The
expanded export specifications refer to the original names of all
entities. The function \texttt{exportInterface} uses the expanded
specifications and the corresponding environments in order to compute
the interface of the module.
\begin{verbatim}

> expandInterface :: CompilerEnv -> Module -> Module
> expandInterface env mdl = expandInterface' mdl (tyConsEnv env)
>                                                (valueEnv env)

> expandInterface' :: Module -> TCEnv -> ValueEnv -> Module
> expandInterface' (Module m es is ds) tcEnv tyEnv =
>   case findDouble exportedTypes of
>     Just tc -> errorMessage $ ambiguousExportType tc
>     Nothing -> case findDouble exportedValues of
>       Just v  -> errorMessage $ ambiguousExportValue v
>       Nothing -> Module m (Just (Exporting NoPos expandedExports)) is ds
>   where
>   expandedExports = joinExports
>                   $ maybe (expandLocalModule          tcEnv tyEnv)
>                           (expandSpecs importedMods m tcEnv tyEnv)
>                           es
>   importedMods   = Set.fromList
>                    [fromMaybe m' asM | ImportDecl _ m' _ asM _ <- is]
>   exportedTypes  = [unqualify tc | ExportTypeWith tc _ <- expandedExports]
>   exportedValues = [c | ExportTypeWith _ cs <- expandedExports, c <- cs]
>                 ++ [unqualify f | Export f <- expandedExports]

\end{verbatim}
While checking all export specifications, the compiler expands
specifications of the form \verb|T(..)| into
\texttt{T($C_1,\dots,C_n$)}, where $C_1,\dots,C_n$ are the data
constructors or the record labels of type \texttt{T}, and replaces
an export specification
\verb|module M| by specifications for all entities which are defined
in module \texttt{M} and imported into the current module with their
unqualified name. In order to distinguish exported type constructors
from exported functions, the former are translated into the equivalent
form \verb|T()|. Note that the export specification \texttt{x} may
export a type constructor \texttt{x} \emph{and} a global function
\texttt{x} at the same time.

\em{Note:} This frontend allows redeclaration and export of imported
identifiers.
\begin{verbatim}

> -- |Expand export specification
> expandSpecs :: Set.Set ModuleIdent -> ModuleIdent -> TCEnv -> ValueEnv
>             -> ExportSpec -> [Export]
> expandSpecs ms m tcEnv tyEnv (Exporting _ es) =
>   concatMap (expandExport ms m tcEnv tyEnv) es

> -- |Expand single export
> expandExport :: Set.Set ModuleIdent -> ModuleIdent -> TCEnv -> ValueEnv
>              -> Export -> [Export]
> expandExport _  m tcEnv tyEnv (Export x)
>   = expandThing m tcEnv tyEnv x
> expandExport _  m tcEnv _     (ExportTypeWith tc cs)
>   = expandTypeWith m tcEnv tc cs
> expandExport _  m tcEnv tyEnv (ExportTypeAll tc)
>   = expandTypeAll m tyEnv tcEnv tc
> expandExport ms m tcEnv tyEnv (ExportModule m')
>   | m' == m
>   = (if m' `Set.member` ms then expandModule tcEnv tyEnv m' else []) -- TODO: Can this happen???
>               ++ expandLocalModule tcEnv tyEnv
>   | m' `Set.member` ms
>   = expandModule tcEnv tyEnv m'
>   | otherwise
>   = errorMessage $ moduleNotImported m'

> -- |Expand export of type cons / data cons / function
> expandThing :: ModuleIdent -> TCEnv -> ValueEnv -> QualIdent -> [Export]
> expandThing m tcEnv tyEnv tc = case qualLookupTC tc tcEnv of
>   []  -> expandThing' m tyEnv tc Nothing
>   [t] -> expandThing' m tyEnv tc (Just [ExportTypeWith (origName t) []])
>   _   -> errorMessage $ ambiguousType tc

> -- |Expand export of data cons / function
> expandThing' :: ModuleIdent -> ValueEnv -> QualIdent -> Maybe [Export]
>              -> [Export]
> expandThing' m tyEnv f tcExport = case qualLookupValue f tyEnv of
>   []             -> fromMaybe (errorMessage $ undefinedEntity f) tcExport
>   [Value f' _ _] -> Export f' : fromMaybe [] tcExport
>   [_]            -> fromMaybe (errorMessage $ exportDataConstr f) tcExport
>   _              -> case qualLookupValue (qualQualify m f) tyEnv of
>     []             -> fromMaybe (errorMessage $ undefinedEntity f) tcExport
>     [Value f' _ _] -> Export f' : fromMaybe [] tcExport
>     [_]            -> fromMaybe (errorMessage $ exportDataConstr f) tcExport
>     _              -> errorMessage $ ambiguousName f

> -- |Expand type constructor with explicit data constructors
> expandTypeWith :: ModuleIdent -> TCEnv -> QualIdent -> [Ident] -> [Export]
> expandTypeWith _ tcEnv tc cs = case qualLookupTC tc tcEnv of
>   [] -> errorMessage $ undefinedType tc
>   [t] | isDataType t   -> [ ExportTypeWith (origName t)
>                           $ map (checkConstr $ constrs t) $ nub cs]
>       | isRecordType t -> [ ExportTypeWith (origName t)
>                           $ map (checkLabel  $ labels  t) $ nub cs]
>       | otherwise      -> errorMessage $ nonDataType tc
>   _  -> errorMessage $ ambiguousType tc
>   where
>     checkConstr cs' c
>       | c `elem` cs' = c
>       | otherwise    = errorMessage $ undefinedDataConstr tc c
>     checkLabel ls l
>       | l' `elem` ls = l'
>       | otherwise    = errorMessage $ undefinedLabel tc l
>       where l' = renameLabel l

> -- |Expand type constructor with all data constructors
> expandTypeAll :: ModuleIdent -> ValueEnv -> TCEnv -> QualIdent -> [Export]
> expandTypeAll _ tyEnv tcEnv tc = case qualLookupTC tc tcEnv of
>   [] -> errorMessage $ undefinedType tc
>   [t] | isDataType t   -> [exportType tyEnv t]
>       | isRecordType t -> exportRecord t
>       | otherwise      -> errorMessage $ nonDataType tc
>   _ -> errorMessage $ ambiguousType tc

> expandLocalModule :: TCEnv -> ValueEnv -> [Export]
> expandLocalModule tcEnv tyEnv =
>   [exportType tyEnv t | (_,t) <- localBindings tcEnv] ++
>   [Export f' | (f,Value f' _ _) <- localBindings tyEnv, f == unRenameIdent f]

> -- |Expand a module export
> expandModule :: TCEnv -> ValueEnv -> ModuleIdent -> [Export]
> expandModule tcEnv tyEnv m =
>   [exportType tyEnv t | (_,t) <- moduleImports m tcEnv] ++
>   [Export f | (_,Value f _ _) <- moduleImports m tyEnv]

> exportType :: ValueEnv -> TypeInfo -> Export
> exportType tyEnv t
>   | isRecordType t -- = ExportTypeWith (origName t) (labels t)
>   = let ls = labels t
>         r  = origName t
>     in case lookupValue (head ls) tyEnv of
>       [Label _ r' _] -> if r == r' then ExportTypeWith r ls
>                                    else ExportTypeWith r []
>       _              -> internalError "Exports.exportType"
>   | otherwise = ExportTypeWith (origName t) (constrs t)

> exportRecord :: TypeInfo -> [Export]
> exportRecord t = [ExportTypeWith (origName t) $ labels t]

\end{verbatim}
The expanded list of exported entities may contain duplicates. These
are removed by the function \texttt{joinExports}.
\begin{verbatim}

> joinExports :: [Export] -> [Export]
> joinExports es =  [ExportTypeWith tc cs | (tc, cs) <- joinedTypes]
>                ++ [Export f             | f        <- joinedFuncs]
>   where joinedTypes = Map.toList $ foldr joinType Map.empty es
>         joinedFuncs = Set.toList $ foldr joinFun  Set.empty es

> joinType :: Export -> Map.Map QualIdent [Ident] -> Map.Map QualIdent [Ident]
> joinType (Export             _) tcs = tcs
> joinType (ExportTypeWith tc cs) tcs = Map.insertWith union tc cs tcs
> joinType _                        _ = internalError
>   "Exports.joinType: no pattern match" -- TODO

> joinFun :: Export -> Set.Set QualIdent -> Set.Set QualIdent
> joinFun (Export           f) fs = f `Set.insert` fs
> joinFun (ExportTypeWith _ _) fs = fs
> joinFun _                     _ = internalError
>   "Exports.joinFun: no pattern match" -- TODO

\end{verbatim}
After checking that the interface is not ambiguous, the compiler
generates the interface's declarations from the list of exported
functions and values. In order to make the interface more stable
against private changes in the module, we remove the hidden data
constructors of a data type in the interface when they occur
right-most in the declaration. In addition, newtypes whose constructor
is not exported are transformed into (abstract) data types.

If a type is imported from another module, its name is qualified with
the name of the module where it is defined. The same applies to an
exported function.
\begin{verbatim}

> exportInterface :: CompilerEnv -> Module -> Interface
> exportInterface env mdl = exportInterface' mdl
>   (opPrecEnv env) (tyConsEnv env) (valueEnv env)

> exportInterface' :: Module -> PEnv -> TCEnv -> ValueEnv -> Interface
> exportInterface' (Module m (Just (Exporting _ es)) _ _) pEnv tcEnv tyEnv
>   = Interface m imports $ precs ++ hidden ++ decls
>   where
>   imports = map   (IImportDecl NoPos) $ usedModules decls
>   precs   = foldr (infixDecl m pEnv) [] es
>   hidden  = map   (hiddenTypeDecl m tcEnv) $ hiddenTypes decls
>   decls   = foldr (typeDecl m tcEnv) (foldr (funDecl m tyEnv) [] es) es
> exportInterface' (Module _ Nothing _ _) _ _ _
>   = internalError "Exports.exportInterface: no export specification"

> infixDecl :: ModuleIdent -> PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl m pEnv (Export             f) ds = iInfixDecl m pEnv f ds
> infixDecl m pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl m pEnv . qualifyLike (qualidMod tc)) ds cs
>   where qualifyLike = maybe qualify qualifyWith
> infixDecl _ _ _ _ = error "Exports.infixDecl: no pattern match"

> iInfixDecl :: ModuleIdent -> PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl m pEnv op ds = case qualLookupP op pEnv of
>   []                           -> ds
>   [PrecInfo _ (OpPrec fix pr)] ->
>     IInfixDecl NoPos fix pr (qualUnqualify m op) : ds
>   _                            -> internalError "Exports.infixDecl"

> typeDecl :: ModuleIdent -> TCEnv -> Export -> [IDecl] -> [IDecl]
> typeDecl _ _     (Export             _) ds = ds
> typeDecl m tcEnv (ExportTypeWith tc cs) ds = case qualLookupTC tc tcEnv of
>   [DataType tc' n cs'] ->
>     iTypeDecl IDataDecl m tc' n
>        (constrDecls m (drop n identSupply) cs cs') : ds
>   [RenamingType tc' n (DataConstr c n' [ty])]
>     | c `elem` cs ->
>         iTypeDecl INewtypeDecl m tc' n (NewConstrDecl NoPos tvs c ty') : ds
>     | otherwise -> iTypeDecl IDataDecl m tc' n [] : ds
>     where tvs = take n' (drop n identSupply)
>           ty' = fromQualType m ty
>   [AliasType tc' n ty] -> case ty of
>     TypeRecord fs _ ->
>         let ty' = TypeRecord (filter (\ (l,_) -> elem l cs) fs) Nothing
>         in  iTypeDecl ITypeDecl m tc' n (fromQualType m ty') : ds
>     _ -> iTypeDecl ITypeDecl m tc' n (fromQualType m ty) : ds
>   _ -> internalError "Exports.typeDecl"
> typeDecl _ _ _ _ = error "Exports.typeDecl: no pattern match"

> iTypeDecl :: (Position -> QualIdent -> [Ident] -> a -> IDecl)
>            -> ModuleIdent -> QualIdent -> Int -> a -> IDecl
> iTypeDecl f m tc n = f NoPos (qualUnqualify m tc) (take n identSupply)

> constrDecls :: ModuleIdent -> [Ident] -> [Ident] -> [Maybe DataConstr]
>             -> [Maybe ConstrDecl]
> constrDecls m tvs cs = clean . map (>>= constrDecl m tvs)
>   where clean = reverse . dropWhile isNothing . reverse
>         constrDecl m' tvs' (DataConstr c n tys)
>           | c `elem` cs =
>               Just (iConstrDecl (take n tvs') c (map (fromQualType m') tys))
>           | otherwise = Nothing

> iConstrDecl :: [Ident] -> Ident -> [TypeExpr] -> ConstrDecl
> iConstrDecl tvs op [ty1,ty2]
>   | isInfixOp op = ConOpDecl NoPos tvs ty1 op ty2
> iConstrDecl tvs c tys = ConstrDecl NoPos tvs c tys

> funDecl :: ModuleIdent -> ValueEnv -> Export -> [IDecl] -> [IDecl]
> funDecl m tyEnv (Export f) ds = case qualLookupValue f tyEnv of
>   [Value _ a (ForAll _ ty)] ->
>     IFunctionDecl NoPos (qualUnqualify m f) a (fromQualType m ty) : ds
>   _ -> internalError $ "Exports.funDecl: " ++ show f
> funDecl _ _     (ExportTypeWith _ _) ds = ds
> funDecl _ _ _ _ = internalError "Exports.funDecl: no pattern match"


\end{verbatim}
The compiler determines the list of imported modules from the set of
module qualifiers that are used in the interface. Careful readers
probably will have noticed that the functions above carefully strip
the module prefix from all entities that are defined in the current
module. Note that the list of modules returned from
\texttt{usedModules} is not necessarily a subset of the modules that
were imported into the current module. This will happen when an
imported module re-exports entities from another module. E.g., given
the three modules
\begin{verbatim}
module A where { data A = A; }
module B(A(..)) where { import A; }
module C where { import B; x = A; }
\end{verbatim}
the interface for module \texttt{C} will import module \texttt{A} but
not module \texttt{B}.
\begin{verbatim}

> usedModules :: [IDecl] -> [ModuleIdent]
> usedModules ds = nub' (catMaybes (map qualidMod (foldr identsDecl [] ds)))
>   where nub' = Set.toList . Set.fromList

> identsDecl :: IDecl -> [QualIdent] -> [QualIdent]
> identsDecl (IDataDecl    _ tc _ cs) xs =
>   tc : foldr identsConstrDecl xs (catMaybes cs)
> identsDecl (INewtypeDecl _ tc _ nc) xs = tc : identsNewConstrDecl nc xs
> identsDecl (ITypeDecl    _ tc _ ty) xs = tc : identsType ty xs
> identsDecl (IFunctionDecl _ f _ ty) xs = f  : identsType ty xs
> identsDecl _ _ = internalError "Exports.identsDecl: no pattern match"

> identsConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
> identsConstrDecl (ConstrDecl    _ _ _ tys) xs = foldr identsType xs tys
> identsConstrDecl (ConOpDecl _ _ ty1 _ ty2) xs =
>   identsType ty1 (identsType ty2 xs)

> identsNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
> identsNewConstrDecl (NewConstrDecl _ _ _ ty) xs = identsType ty xs

> identsType :: TypeExpr -> [QualIdent] -> [QualIdent]
> identsType (ConstructorType tc tys) xs = tc : foldr identsType xs tys
> identsType (VariableType         _) xs = xs
> identsType (TupleType          tys) xs = foldr identsType xs tys
> identsType (ListType            ty) xs = identsType ty xs
> identsType (ArrowType      ty1 ty2) xs = identsType ty1 (identsType ty2 xs)
> identsType (RecordType      fs rty) xs =
>   foldr identsType (maybe xs (\ty -> identsType ty xs) rty) (map snd fs)

\end{verbatim}
After the interface declarations have been computed, the compiler
eventually must add hidden (data) type declarations to the interface
for all those types which were used in the interface but not exported
from the current module, so that these type constructors can always be
distinguished from type variables.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tc = case qualLookupTC (qualQualify m tc) tcEnv of
>   [DataType     _ n _] -> hidingDataDecl tc n
>   [RenamingType _ n _] -> hidingDataDecl tc n
>   _                    -> internalError "Exports.hiddenTypeDecl"
>   where hidingDataDecl tc1 n = HidingDataDecl NoPos (unqualify tc1)
>                              $ take n identSupply

> hiddenTypes :: [IDecl] -> [QualIdent]
> hiddenTypes ds = [tc | tc <- Set.toList tcs, not (isQualified tc)]
>   where tcs = foldr Set.delete (Set.fromList $ usedTypes ds)
>                     (definedTypes ds)

> usedTypes :: [IDecl] -> [QualIdent]
> usedTypes ds = foldr usedTypesDecl [] ds

> usedTypesDecl :: IDecl -> [QualIdent] -> [QualIdent]
> usedTypesDecl (IDataDecl     _ _ _ cs) tcs =
>   foldr usedTypesConstrDecl tcs (catMaybes cs)
> usedTypesDecl (INewtypeDecl  _ _ _ nc) tcs = usedTypesNewConstrDecl nc tcs
> usedTypesDecl (ITypeDecl     _ _ _ ty) tcs = usedTypesType ty tcs
> usedTypesDecl (IFunctionDecl _ _ _ ty) tcs = usedTypesType ty tcs
> usedTypesDecl _                        _   = internalError
>   "Exports.usedTypesDecl: no pattern match" -- TODO

> usedTypesConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
> usedTypesConstrDecl (ConstrDecl    _ _ _ tys) tcs =
>   foldr usedTypesType tcs tys
> usedTypesConstrDecl (ConOpDecl _ _ ty1 _ ty2) tcs =
>   usedTypesType ty1 (usedTypesType ty2 tcs)

> usedTypesNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
> usedTypesNewConstrDecl (NewConstrDecl _ _ _ ty) tcs = usedTypesType ty tcs

> usedTypesType :: TypeExpr -> [QualIdent] -> [QualIdent]
> usedTypesType (ConstructorType tc tys) tcs =
>   tc : foldr usedTypesType tcs tys
> usedTypesType (VariableType         _) tcs = tcs
> usedTypesType (TupleType          tys) tcs = foldr usedTypesType tcs tys
> usedTypesType (ListType            ty) tcs = usedTypesType ty tcs
> usedTypesType (ArrowType      ty1 ty2) tcs =
>   usedTypesType ty1 (usedTypesType ty2 tcs)
> usedTypesType (RecordType      fs rty) tcs =
>   foldr usedTypesType (maybe tcs (\ty -> usedTypesType ty tcs) rty)
>         (map snd fs)

> definedTypes :: [IDecl] -> [QualIdent]
> definedTypes ds = foldr definedType [] ds

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl    _ tc _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _) tcs = tc : tcs
> definedType (ITypeDecl    _ tc _ _) tcs = tc : tcs
> definedType (IFunctionDecl _ _ _ _) tcs = tcs
> definedType _                       tcs = tcs

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> isDataType :: TypeInfo -> Bool
> isDataType (DataType     _ _ _) = True
> isDataType (RenamingType _ _ _) = True
> isDataType (AliasType    _ _ _) = False

> isRecordType :: TypeInfo -> Bool
> isRecordType (AliasType _ _ (TypeRecord _ _)) = True
> isRecordType _                                = False

> constrs :: TypeInfo -> [Ident]
> constrs (DataType _ _ cs)                     =
>   [c | Just (DataConstr c _ _) <- cs]
> constrs (RenamingType _ _ (DataConstr c _ _)) = [c]
> constrs (AliasType _ _ _)                     = []

> labels :: TypeInfo -> [Ident]
> labels (AliasType _ _ (TypeRecord fs _)) = map fst fs
> labels _                                 = []

\end{verbatim}
Error messages
\begin{verbatim}

> undefinedEntity :: QualIdent -> Message
> undefinedEntity x = qposErr x $
>   "Entity " ++ qualName x ++ " in export list is not defined"

> undefinedType :: QualIdent -> Message
> undefinedType tc = qposErr tc $
>   "Type " ++ qualName tc ++ " in export list is not defined"

> moduleNotImported :: ModuleIdent -> Message
> moduleNotImported m = toMessage (positionOfModuleIdent m) $
>   "Module " ++ moduleName m ++ " not imported"

> ambiguousExportType :: Ident -> Message
> ambiguousExportType x = posErr x $ "Ambiguous export of type " ++ name x

> ambiguousExportValue :: Ident -> Message
> ambiguousExportValue x = posErr x $ "Ambiguous export of " ++ name x

> ambiguousType :: QualIdent -> Message
> ambiguousType tc = qposErr tc $ "Ambiguous type " ++ qualName tc

> ambiguousName :: QualIdent -> Message
> ambiguousName x = qposErr x $ "Ambiguous name " ++ qualName x

> exportDataConstr :: QualIdent -> Message
> exportDataConstr c = qposErr c $
>   "Data constructor " ++ qualName c ++ " in export list"

> nonDataType :: QualIdent -> Message
> nonDataType tc = qposErr tc $ qualName tc ++ " is not a data type"

> undefinedDataConstr :: QualIdent -> Ident -> Message
> undefinedDataConstr tc c = posErr c $
>   name c ++ " is not a data constructor of type " ++ qualName tc

> undefinedLabel :: QualIdent -> Ident -> Message
> undefinedLabel r l = posErr l $
>   name l ++ " is not a label of the record " ++ qualName r

\end{verbatim}
