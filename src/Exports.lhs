% -*- LaTeX -*-
% $Id: Exports.lhs,v 1.32 2004/02/13 19:23:57 wlux Exp $
%
% Copyright (c) 2000-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Exports.lhs}
\section{Creating Interfaces}
This section describes how the exported interface of a compiled module
is computed.
\begin{verbatim}

> module Exports(expandInterface,exportInterface) where
> import Base
> import List
> import Map
> import Maybe
> import Set
> import TopEnv

\end{verbatim}
The interface of a module is computed in two steps. The function
\texttt{expandInterface} checks the export specifications of the
module and expands them into a list containing all exported types and
functions, combining multiple exports for the same entity. The
expanded export specifications refer to the original names of all
entities. The function \texttt{exportInterface} uses the expanded
specifications and the corresponding environments in order to compute
to the interface of the module.
\begin{verbatim}

> expandInterface :: Module -> TCEnv -> ValueEnv -> Module
> expandInterface (Module m es ds) tcEnv tyEnv =
>   case linear [unqualify tc | ExportTypeWith tc _ <- es'] of
>     Linear ->
>       case linear ([c | ExportTypeWith _ cs <- es', c <- cs] ++
>                    [unqualify f | Export f <- es']) of
>         Linear -> Module m (Just (Exporting noPos es')) ds
>         NonLinear v -> error (ambiguousExportValue v)
>     NonLinear tc -> error (ambiguousExportType tc)
>   where ms = fromListSet [fromMaybe m asM | ImportDecl _ m _ asM _ <- ds]
>         es' = joinExports $                                              -- $
>               maybe (expandLocalModule tcEnv tyEnv)
>                     (expandSpecs ms m tcEnv tyEnv)
>                     es

\end{verbatim}
While checking all export specifications, the compiler expands
specifications of the form \verb|T(..)| into
\texttt{T($C_1,\dots,C_n$)}, where $C_1,\dots,C_n$ are the data
constructors of type \texttt{T}, and replaces an export specification
\verb|module M| by specifications for all entities which are defined
in module \texttt{M} and imported into the current module with their
unqualified name. In order to distinguish exported type constructors
from exported functions, the former are translated into the equivalent
form \verb|T()|. Note that the export specification \texttt{x} may
export a type constructor \texttt{x} \emph{and} a global function
\texttt{x} at the same time.
\begin{verbatim}

> expandSpecs :: Set ModuleIdent -> ModuleIdent -> TCEnv -> ValueEnv
>             -> ExportSpec -> [Export]
> expandSpecs ms m tcEnv tyEnv (Exporting p es) =
>   concat (map (expandExport p ms m tcEnv tyEnv) es)

> expandExport :: Position -> Set ModuleIdent -> ModuleIdent -> TCEnv
>              -> ValueEnv -> Export -> [Export]
> expandExport p _ _ tcEnv tyEnv (Export x) = expandThing p tcEnv tyEnv x
> expandExport p _ _ tcEnv _ (ExportTypeWith tc cs) =
>   [expandTypeWith p tcEnv tc cs]
> expandExport p _ _ tcEnv _ (ExportTypeAll tc) = [expandTypeAll p tcEnv tc]
> expandExport p ms m tcEnv tyEnv (ExportModule m')
>   | m == m' = (if m `elemSet` ms then expandModule tcEnv tyEnv m else [])
>               ++ expandLocalModule tcEnv tyEnv
>   | m' `elemSet` ms = expandModule tcEnv tyEnv m'
>   | otherwise = errorAt p (moduleNotImported m')

> expandThing :: Position -> TCEnv -> ValueEnv -> QualIdent -> [Export]
> expandThing p tcEnv tyEnv tc =
>   case qualLookupTC tc tcEnv of
>     [] -> expandThing' p tyEnv tc Nothing
>     [t] -> expandThing' p tyEnv tc (Just [ExportTypeWith (origName t) []])
>     _ -> errorAt p (ambiguousType tc)

> expandThing' :: Position -> ValueEnv -> QualIdent -> Maybe [Export]
>              -> [Export]
> expandThing' p tyEnv f tcExport =
>   case qualLookupValue f tyEnv of
>     [] -> fromMaybe (errorAt p (undefinedEntity f)) tcExport
>     [Value f' _] -> Export f' : fromMaybe [] tcExport
>     [_] -> fromMaybe (errorAt p (exportDataConstr f)) tcExport
>     _ -> errorAt p (ambiguousName f)

> expandTypeWith :: Position -> TCEnv -> QualIdent -> [Ident] -> Export
> expandTypeWith p tcEnv tc cs =
>   case qualLookupTC tc tcEnv of
>     [] -> errorAt p (undefinedType tc)
>     [t]
>       | isDataType t -> ExportTypeWith (origName t)
>                           (map (checkConstr (constrs t)) (nub cs))
>       | otherwise -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)
>   where checkConstr cs c
>           | c `elem` cs = c
>           | otherwise = errorAt p (undefinedDataConstr tc c)

> expandTypeAll :: Position -> TCEnv -> QualIdent -> Export
> expandTypeAll p tcEnv tc =
>   case qualLookupTC tc tcEnv of
>     [] -> errorAt p (undefinedType tc)
>     [t]
>       | isDataType t -> exportType t 
>       | otherwise -> errorAt p (nonDataType tc)
>     _ -> errorAt p (ambiguousType tc)

> expandLocalModule :: TCEnv -> ValueEnv -> [Export]
> expandLocalModule tcEnv tyEnv =
>   [exportType t | (_,t) <- localBindings tcEnv] ++
>   [Export f' | (f,Value f' _) <- localBindings tyEnv, f == unRenameIdent f]

> expandModule :: TCEnv -> ValueEnv -> ModuleIdent -> [Export]
> expandModule tcEnv tyEnv m =
>   [exportType t | (_,t) <- moduleImports m tcEnv] ++
>   [Export f | (_,Value f _) <- moduleImports m tyEnv]

> exportType :: TypeInfo -> Export
> exportType t = ExportTypeWith (origName t) (constrs t)

\end{verbatim}
The expanded list of exported entities may contain duplicates. These
are removed by the function \texttt{joinExports}.
\begin{verbatim}

> joinExports :: [Export] -> [Export]
> joinExports es =
>   [ExportTypeWith tc cs | (tc,cs) <- toListFM (foldr joinType zeroFM es)] ++
>   [Export f | f <- toListSet (foldr joinFun zeroSet es)]

> joinType :: Export -> FM QualIdent [Ident] -> FM QualIdent [Ident]
> joinType (Export _) tcs = tcs
> joinType (ExportTypeWith tc cs) tcs =
>   addToFM tc (cs `union` fromMaybe [] (lookupFM tc tcs)) tcs

> joinFun :: Export -> Set QualIdent -> Set QualIdent
> joinFun (Export f) fs = f `addToSet` fs
> joinFun (ExportTypeWith _ _) fs = fs

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

> exportInterface :: Module -> PEnv -> TCEnv -> ValueEnv -> Interface
> exportInterface (Module m (Just (Exporting _ es)) _) pEnv tcEnv tyEnv =
>   Interface m (imports ++ precs ++ hidden ++ ds)
>   where imports = map (IImportDecl noPos) (usedModules ds)
>         precs = foldr (infixDecl m pEnv) [] es
>         hidden = map (hiddenTypeDecl m tcEnv) (hiddenTypes ds)
>         ds = foldr (typeDecl m tcEnv) (foldr (funDecl m tyEnv) [] es) es
> exportInterface (Module _ Nothing _) _ _ _ = internalError "exportInterface"

> infixDecl :: ModuleIdent -> PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl m pEnv (Export f) ds = iInfixDecl m pEnv f ds
> infixDecl m pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl m pEnv . qualifyLike (fst (splitQualIdent tc))) ds cs
>   where qualifyLike = maybe qualify qualifyWith

> iInfixDecl :: ModuleIdent -> PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl m pEnv op ds =
>   case qualLookupP op pEnv of
>     [] -> ds
>     [PrecInfo _ (OpPrec fix pr)] ->
>       IInfixDecl noPos fix pr (qualUnqualify m op) : ds
>     _ -> internalError "infixDecl"

> typeDecl :: ModuleIdent -> TCEnv -> Export -> [IDecl] -> [IDecl]
> typeDecl _ _ (Export _) ds = ds
> typeDecl m tcEnv (ExportTypeWith tc cs) ds =
>   case qualLookupTC tc tcEnv of
>     [DataType tc n cs'] ->
>       iTypeDecl IDataDecl m tc n
>          (constrDecls m (drop n nameSupply) cs cs') : ds
>     [RenamingType tc n (Data c n' ty)]
>       | c `elem` cs ->
>           iTypeDecl INewtypeDecl m tc n (NewConstrDecl noPos tvs c ty') : ds
>       | otherwise -> iTypeDecl IDataDecl m tc n [] : ds
>       where tvs = take n' (drop n nameSupply)
>             ty' = fromQualType m ty
>     [AliasType tc n ty] ->
>       iTypeDecl ITypeDecl m tc n (fromQualType m ty) : ds
>     _ -> internalError "typeDecl"

> iTypeDecl :: (Position -> QualIdent -> [Ident] -> a -> IDecl)
>            -> ModuleIdent -> QualIdent -> Int -> a -> IDecl
> iTypeDecl f m tc n = f noPos (qualUnqualify m tc) (take n nameSupply)

> constrDecls :: ModuleIdent -> [Ident] -> [Ident] -> [Maybe (Data [Type])]
>             -> [Maybe ConstrDecl]
> constrDecls m tvs cs = clean . map (>>= constrDecl m tvs)
>   where clean = reverse . dropWhile isNothing . reverse
>         constrDecl m tvs (Data c n tys)
>           | c `elem` cs =
>               Just (iConstrDecl (take n tvs) c (map (fromQualType m) tys))
>           | otherwise = Nothing

> iConstrDecl :: [Ident] -> Ident -> [TypeExpr] -> ConstrDecl
> iConstrDecl tvs op [ty1,ty2]
>   | isInfixOp op = ConOpDecl noPos tvs ty1 op ty2
> iConstrDecl tvs c tys = ConstrDecl noPos tvs c tys

> funDecl :: ModuleIdent -> ValueEnv -> Export -> [IDecl] -> [IDecl]
> funDecl m tyEnv (Export f) ds =
>   case qualLookupValue f tyEnv of
>     [Value _ (ForAll _ ty)] ->
>       IFunctionDecl noPos (qualUnqualify m f) (fromQualType m ty) : ds
>     _ -> internalError "funDecl"
> funDecl _ _ (ExportTypeWith _ _) ds = ds

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
> usedModules ds = nub (catMaybes (map modul (foldr identsDecl [] ds)))
>   where nub = toListSet . fromListSet
>         modul = fst . splitQualIdent

> identsDecl :: IDecl -> [QualIdent] -> [QualIdent]
> identsDecl (IDataDecl _ tc _ cs) xs =
>   tc : foldr identsConstrDecl xs (catMaybes cs)
> identsDecl (INewtypeDecl _ tc _ nc) xs = tc : identsNewConstrDecl nc xs
> identsDecl (ITypeDecl _ tc _ ty) xs = tc : identsType ty xs
> identsDecl (IFunctionDecl _ f ty) xs = f : identsType ty xs

> identsConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
> identsConstrDecl (ConstrDecl _ _ _ tys) xs = foldr identsType xs tys
> identsConstrDecl (ConOpDecl _ _ ty1 _ ty2) xs =
>   identsType ty1 (identsType ty2 xs)

> identsNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
> identsNewConstrDecl (NewConstrDecl _ _ _ ty) xs = identsType ty xs

> identsType :: TypeExpr -> [QualIdent] -> [QualIdent]
> identsType (ConstructorType tc tys) xs = tc : foldr identsType xs tys
> identsType (VariableType _) xs = xs
> identsType (TupleType tys) xs = foldr identsType xs tys
> identsType (ListType ty) xs = identsType ty xs
> identsType (ArrowType ty1 ty2) xs = identsType ty1 (identsType ty2 xs)

\end{verbatim}
After the interface declarations have been computed, the compiler
eventually must add hidden (data) type declarations to the interface
for all those types which were used in the interface but not exported
from the current module, so that these type constructors can always be
distinguished from type variables.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tc =
>   case qualLookupTC (qualQualify m tc) tcEnv of
>     [DataType _ n _] -> hidingDataDecl tc n
>     [RenamingType _ n _] -> hidingDataDecl tc n
>     _ ->  internalError "hiddenTypeDecl"
>   where hidingDataDecl tc n =
>           HidingDataDecl noPos (unqualify tc) (take n nameSupply)

> hiddenTypes :: [IDecl] -> [QualIdent]
> hiddenTypes ds = [tc | tc <- toListSet tcs, not (isQualified tc)]
>   where tcs = foldr deleteFromSet (fromListSet (usedTypes ds))
>                     (definedTypes ds)

> usedTypes :: [IDecl] -> [QualIdent]
> usedTypes ds = foldr usedTypesDecl [] ds

> usedTypesDecl :: IDecl -> [QualIdent] -> [QualIdent]
> usedTypesDecl (IDataDecl _ _ _ cs) tcs =
>   foldr usedTypesConstrDecl tcs (catMaybes cs)
> usedTypesDecl (INewtypeDecl _ _ _ nc) tcs = usedTypesNewConstrDecl nc tcs
> usedTypesDecl (ITypeDecl _ _ _ ty) tcs = usedTypesType ty tcs
> usedTypesDecl (IFunctionDecl _ _ ty) tcs = usedTypesType ty tcs

> usedTypesConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
> usedTypesConstrDecl (ConstrDecl _ _ _ tys) tcs = foldr usedTypesType tcs tys
> usedTypesConstrDecl (ConOpDecl _ _ ty1 _ ty2) tcs =
>   usedTypesType ty1 (usedTypesType ty2 tcs)

> usedTypesNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
> usedTypesNewConstrDecl (NewConstrDecl _ _ _ ty) tcs = usedTypesType ty tcs

> usedTypesType :: TypeExpr -> [QualIdent] -> [QualIdent]
> usedTypesType (ConstructorType tc tys) tcs = tc : foldr usedTypesType tcs tys
> usedTypesType (VariableType _) tcs = tcs
> usedTypesType (TupleType tys) tcs = foldr usedTypesType tcs tys
> usedTypesType (ListType ty) tcs = usedTypesType ty tcs
> usedTypesType (ArrowType ty1 ty2) tcs =
>   usedTypesType ty1 (usedTypesType ty2 tcs)

> definedTypes :: [IDecl] -> [QualIdent]
> definedTypes ds = foldr definedType [] ds

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ tc _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _) tcs = tc : tcs
> definedType (IFunctionDecl _ _ _)  tcs = tcs

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> noPos :: Position
> noPos = undefined

> isDataType :: TypeInfo -> Bool
> isDataType (DataType _ _ _) = True
> isDataType (RenamingType _ _ _) = True
> isDataType (AliasType _ _ _) = False

> constrs :: TypeInfo -> [Ident]
> constrs (DataType _ _ cs) = [c | Just (Data c _ _) <- cs]
> constrs (RenamingType _ _ (Data c _ _)) = [c]
> constrs (AliasType _ _ _) = []

\end{verbatim}
Error messages
\begin{verbatim}

> undefinedEntity :: QualIdent -> String
> undefinedEntity x =
>   "Entity " ++ qualName x ++ " in export list is not defined"

> undefinedType :: QualIdent -> String
> undefinedType tc = "Type " ++ qualName tc ++ " in export list is not defined"

> moduleNotImported :: ModuleIdent -> String
> moduleNotImported m = "Module " ++ moduleName m ++ " not imported"

> ambiguousExportType :: Ident -> String
> ambiguousExportType x = "Ambiguous export of type " ++ name x

> ambiguousExportValue :: Ident -> String
> ambiguousExportValue x = "Ambiguous export of " ++ name x

> ambiguousType :: QualIdent -> String
> ambiguousType tc = "Ambiguous type " ++ qualName tc

> ambiguousName :: QualIdent -> String
> ambiguousName x = "Ambiguous name " ++ qualName x

> exportDataConstr :: QualIdent -> String
> exportDataConstr c = "Data constructor " ++ qualName c ++ " in export list"

> nonDataType :: QualIdent -> String
> nonDataType tc = qualName tc ++ " is not a data type"

> undefinedDataConstr :: QualIdent -> Ident -> String
> undefinedDataConstr tc c =
>   name c ++ " is not a data constructor of type " ++ qualName tc

\end{verbatim}
