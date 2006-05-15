
% $Id: Imports.lhs,v 1.25 2004/02/13 19:24:00 wlux Exp $
%
% Copyright (c) 2000-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Imports.lhs}
\section{Importing interfaces}
This module provides a few functions which can be used to import
interfaces into the current module.
\begin{verbatim}

> module Imports(importInterface,importInterfaceIntf,importUnifyData) where
> import Base
> import Env
> import TopEnv
> import Maybe
> import Map
> import Set

\end{verbatim}
Four kinds of environments are computed from the interface, one
containing the operator precedences, another for the type
constructors, the third containing the types of the data
constructors and functions, and the last contains the arity for each
function and constructor. Note that the original names of all
entities defined in the imported module are qualified appropriately.
The same is true for type expressions.
\begin{verbatim}

> type ExpPEnv = Env Ident PrecInfo
> type ExpTCEnv = Env Ident TypeInfo
> type ExpValueEnv = Env Ident ValueInfo
> type ExpArityEnv = Env Ident ArityInfo

\end{verbatim}
When an interface is imported, the compiler first transforms the
interface into these environments. If an import specification is
present, the environments are restricted to only those entities which
are included in the specification or not hidden by it, respectively.
The resulting environments are then imported into the current module
using either a qualified import or both a qualified and an unqualified
import.
\begin{verbatim}

> importInterface :: Position -> ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> Interface -> PEnv -> TCEnv -> ValueEnv -> ArityEnv
>                 -> (PEnv,TCEnv,ValueEnv,ArityEnv)
> importInterface p m q is i pEnv tcEnv tyEnv aEnv =
>   (importEntities m q vs id mPEnv pEnv,
>    importEntities m q ts (importData vs) mTCEnv tcEnv,
>    importEntities m q vs id mTyEnv tyEnv,
>    importEntities m q as id mAEnv aEnv)
>   where mPEnv  = intfEnv bindPrec i
>         mTCEnv = intfEnv bindTC i
>         mTyEnv = intfEnv bindTy i
>         mAEnv  = intfEnv bindA i
>         is' = maybe [] (expandSpecs m mTCEnv mTyEnv) is
>         ts  = isVisible is (fromListSet (foldr addType [] is'))
>         vs  = isVisible is (fromListSet (foldr addValue [] is'))
>         as  = isVisible is (fromListSet (foldr addArity [] is'))

> isVisible :: Maybe ImportSpec -> Set Ident -> Ident -> Bool
> isVisible (Just (Importing _ _)) xs = (`elemSet` xs)
> isVisible (Just (Hiding _ _)) xs = (`notElemSet` xs)
> isVisible _ _ = const True

> importEntities :: Entity a => ModuleIdent -> Bool -> (Ident -> Bool)
>                -> (a -> a) -> Env Ident a -> TopEnv a -> TopEnv a
> importEntities m q isVisible f mEnv env =
>   foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
>         [(x,f y) | (x,y) <- envToList mEnv, isVisible x]
>   where importUnqual m x y = importTopEnv m x y . qualImportTopEnv m x y

> importData :: (Ident -> Bool) -> TypeInfo -> TypeInfo
> importData isVisible (DataType tc n cs) =
>   DataType tc n (map (>>= importConstr isVisible) cs)
> importData isVisible (RenamingType tc n nc) =
>   maybe (DataType tc n []) (RenamingType tc n) (importConstr isVisible nc)
> importData isVisible (AliasType tc  n ty) = AliasType tc n ty

> importConstr :: (Ident -> Bool) -> Data a -> Maybe (Data a)
> importConstr isVisible (Data c n tys)
>   | isVisible c = Just (Data c n tys)
>   | otherwise = Nothing

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because all entities are imported into the environment. In addition,
only a qualified import is necessary. Note that the hidden data types
are imported as well because they may be used in type expressions in
an interface.
\begin{verbatim}

> importInterfaceIntf :: Interface -> PEnv -> TCEnv -> ValueEnv -> ArityEnv
>                     -> (PEnv,TCEnv,ValueEnv,ArityEnv)
> importInterfaceIntf i pEnv tcEnv tyEnv aEnv =
>   (importEntities m True (const True) id (intfEnv bindPrec i) pEnv,
>    importEntities m True (const True) id (intfEnv bindTCHidden i) tcEnv,
>    importEntities m True (const True) id (intfEnv bindTy i) tyEnv,
>    importEntities m True (const True) id (intfEnv bindA i) aEnv)
>   where Interface m _ = i

\end{verbatim}
In a first step, the three export environments are initialized from
the interface's declarations. This step also qualifies the names of
all entities defined in (but not imported into) the interface with its
module name.  
\begin{verbatim}

> intfEnv :: (ModuleIdent -> IDecl -> Env Ident a -> Env Ident a)
>         -> Interface -> Env Ident a
> intfEnv bind (Interface m ds) = foldr (bind m) emptyEnv ds

> bindPrec :: ModuleIdent -> IDecl -> ExpPEnv -> ExpPEnv
> bindPrec m (IInfixDecl _ fix p op) =
>   bindEnv (unqualify op) (PrecInfo (qualQualify m op) (OpPrec fix p))
> bindPrec _ _ = id

> bindTC :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
> bindTC m (IDataDecl _ tc tvs cs) mTCEnv 
>   | isJust (lookupEnv (unqualify tc) mTCEnv) =
>     mTCEnv
>   | otherwise =
>     bindType DataType m tc tvs (map (fmap mkData) cs) mTCEnv
>   where mkData (ConstrDecl _ evs c tys) =
>           Data c (length evs) (toQualTypes m tvs tys)
>         mkData (ConOpDecl _ evs ty1 c ty2) =
>           Data c (length evs) (toQualTypes m tvs [ty1,ty2])
> bindTC m (INewtypeDecl _ tc tvs (NewConstrDecl _ evs c ty)) mTCEnv =
>   bindType RenamingType m tc tvs 
>	 (Data c (length evs) (toQualType m tvs ty)) mTCEnv
> bindTC m (ITypeDecl _ tc tvs ty) mTCEnv
>   | isRecordExtId tc' = 
>     bindType AliasType m (qualify (fromRecordExtId tc')) tvs 
>	   (toQualType m tvs ty) mTCEnv
>   | otherwise =
>     bindType AliasType m tc tvs (toQualType m tvs ty) mTCEnv
>   where tc' = unqualify tc
> bindTC m _ mTCEnv = mTCEnv

> bindTCHidden :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
> bindTCHidden m (HidingDataDecl _ tc tvs) =
>   bindType DataType m (qualify tc) tvs []
> bindTCHidden m d = bindTC m d

> bindType :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent -> QualIdent
>          -> [Ident] -> a -> ExpTCEnv -> ExpTCEnv
> bindType f m tc tvs =
>   bindEnv (unqualify tc) . f (qualQualify m tc) (length tvs) 

> bindTy :: ModuleIdent -> IDecl -> ExpValueEnv -> ExpValueEnv
> bindTy m (IDataDecl _ tc tvs cs) =
>   flip (foldr (bindConstr m tc' tvs (constrType tc' tvs))) (catMaybes cs)
>   where tc' = qualQualify m tc
> bindTy m (INewtypeDecl _ tc tvs nc) =
>   bindNewConstr m tc' tvs (constrType tc' tvs) nc
>   where tc' = qualQualify m tc
> --bindTy m (ITypeDecl _ r tvs (RecordType fs _)) =
> --  flip (foldr (bindRecLabel m r')) fs
> --  where r' = qualifyWith m (fromRecordExtId (unqualify r))
> bindTy m (IFunctionDecl _ f _ ty) =
>   bindEnv (unqualify f)
>           (Value (qualQualify m f) (polyType (toQualType m [] ty)))
> bindTy m _ = id

> bindConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl
>            -> ExpValueEnv -> ExpValueEnv
> bindConstr m tc tvs ty0 (ConstrDecl _ evs c tys) =
>   bindValue DataConstructor m tc tvs c evs (foldr ArrowType ty0 tys)
> bindConstr m tc tvs ty0 (ConOpDecl _ evs ty1 op ty2) =
>   bindValue DataConstructor m tc tvs op evs
>             (ArrowType ty1 (ArrowType ty2 ty0))

> bindNewConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr
>               -> NewConstrDecl -> ExpValueEnv -> ExpValueEnv
> bindNewConstr m tc tvs ty0 (NewConstrDecl _ evs c ty1) =
>   bindValue NewtypeConstructor m tc tvs c evs (ArrowType ty1 ty0)

> --bindRecLabel :: ModuleIdent -> QualIdent -> ([Ident],TypeExpr)
> --      -> ExpValueEnv -> ExpValueEnv
> --bindRecLabel m r ([l],ty) =
> --  bindEnv l (Label (qualify l) r (polyType (toQualType m [] ty)))

> bindValue :: (QualIdent -> ExistTypeScheme -> ValueInfo) -> ModuleIdent
>           -> QualIdent -> [Ident] -> Ident -> [Ident] -> TypeExpr
>           -> ExpValueEnv -> ExpValueEnv
> bindValue f m tc tvs c evs ty = bindEnv c (f (qualifyLike tc c) sigma)
>   where sigma = ForAllExist (length tvs) (length evs) (toQualType m tvs ty)
>         qualifyLike x = maybe qualify qualifyWith (fst (splitQualIdent x))

> bindA :: ModuleIdent -> IDecl -> ExpArityEnv -> ExpArityEnv
> bindA m (IDataDecl _ _ _ cs) expAEnv
>    = foldr (bindConstrA m) expAEnv (catMaybes cs)
> bindA m (IFunctionDecl _ f a _) expAEnv
>    = bindEnv (unqualify f) (ArityInfo (qualQualify m f) a) expAEnv
> bindA _ _ expAEnv = expAEnv

> bindConstrA :: ModuleIdent -> ConstrDecl -> ExpArityEnv -> ExpArityEnv
> bindConstrA m (ConstrDecl _ _ c tys) expAEnv
>    = bindEnv c (ArityInfo (qualifyWith m c) (length tys)) expAEnv
> bindConstrA m (ConOpDecl _ _ _ c _) expAEnv
>    = bindEnv c (ArityInfo (qualifyWith m c) 2) expAEnv

\end{verbatim}
After the environments have been initialized, the optional import
specifications can be checked. There are two kinds of import
specifications, a ``normal'' one, which names the entities that shall
be imported, and a hiding specification, which lists those entities
that shall not be imported.

There is a subtle difference between both kinds of
specifications. While it is not allowed to list a data constructor
outside of its type in a ``normal'' specification, it is allowed to
hide a data constructor explicitly. E.g., if module \texttt{A} exports
the data type \texttt{T} with constructor \texttt{C}, the data
constructor can be imported with one of the two specifications
\begin{verbatim}
import A(T(C))
import A(T(..))
\end{verbatim}
but can be hidden in three different ways:
\begin{verbatim}
import A hiding(C)
import A hiding(T(C))
import A hiding(T(..))
\end{verbatim}

The functions \texttt{expandImport} and \texttt{expandHiding} check
that all entities in an import specification are actually exported
from the module. In addition, all imports of type constructors are
changed into a \texttt{T()} specification and explicit imports for the
data constructors are added.
\begin{verbatim}

> expandSpecs :: ModuleIdent -> ExpTCEnv -> ExpValueEnv -> ImportSpec
>             -> [Import]
> expandSpecs m tcEnv tyEnv (Importing p is) =
>   concat (map (expandImport p m tcEnv tyEnv) is)
> expandSpecs m tcEnv tyEnv (Hiding p is) =
>   concat (map (expandHiding p m tcEnv tyEnv) is)

> expandImport :: Position -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Import
>              -> [Import]
> expandImport p m tcEnv tyEnv (Import x) = expandThing p m tcEnv tyEnv x
> expandImport p m tcEnv tyEnv (ImportTypeWith tc cs) =
>   [expandTypeWith p m tcEnv tc cs]
> expandImport p m tcEnv tyEnv (ImportTypeAll tc) =
>   [expandTypeAll p m tcEnv tc]

> expandHiding :: Position -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Import
>              -> [Import]
> expandHiding p m tcEnv tyEnv (Import x) = expandHide p m tcEnv tyEnv x
> expandHiding p m tcEnv tyEnv (ImportTypeWith tc cs) =
>   [expandTypeWith p m tcEnv tc cs]
> expandHiding p m tcEnv tyEnv (ImportTypeAll tc) =
>   [expandTypeAll p m tcEnv tc]

> expandThing :: Position -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Ident
>             -> [Import]
> expandThing p m tcEnv tyEnv tc =
>   case lookupEnv tc tcEnv of
>     Just _ -> expandThing' p m tyEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandThing' p m tyEnv tc Nothing

> expandThing' :: Position -> ModuleIdent -> ExpValueEnv -> Ident
>              -> Maybe [Import] -> [Import]
> expandThing' p m tyEnv f tcImport =
>   case lookupEnv f tyEnv of
>     Just v
>       | isConstr v -> maybe (errorAt p (importDataConstr m f)) id tcImport
>       | otherwise -> Import f : maybe [] id tcImport
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) id tcImport
>   where isConstr (DataConstructor _ _) = True
>         isConstr (NewtypeConstructor _ _) = True
>         isConstr (Value _ _) = False

> expandHide :: Position -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Ident
>            -> [Import]
> expandHide p m tcEnv tyEnv tc =
>   case lookupEnv tc tcEnv of
>     Just _ -> expandHide' p m tyEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandHide' p m tyEnv tc Nothing

> expandHide' :: Position -> ModuleIdent -> ExpValueEnv -> Ident
>             -> Maybe [Import] -> [Import]
> expandHide' p m tyEnv f tcImport =
>   case lookupEnv f tyEnv of
>     Just _ -> Import f : maybe [] id tcImport
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) id tcImport

> expandTypeWith :: Position -> ModuleIdent -> ExpTCEnv -> Ident -> [Ident]
>                -> Import
> expandTypeWith p m tcEnv tc cs =
>   case lookupEnv tc tcEnv of
>     Just (DataType _ _ cs') ->
>       ImportTypeWith tc (map (checkConstr [c | Just (Data c _ _) <- cs']) cs)
>     Just (RenamingType _ _ (Data c _ _)) ->
>       ImportTypeWith tc (map (checkConstr [c]) cs)
>     Just _ -> errorAt p (nonDataType m tc)
>     Nothing -> errorAt p (undefinedEntity m tc)
>   where checkConstr cs c
>           | c `elem` cs = c
>           | otherwise = errorAt p (undefinedDataConstr m tc c)

> expandTypeAll :: Position -> ModuleIdent -> ExpTCEnv -> Ident -> Import
> expandTypeAll p m tcEnv tc =
>   case lookupEnv tc tcEnv of
>     Just (DataType _ _ cs) -> ImportTypeWith tc [c | Just (Data c _ _) <- cs]
>     Just (RenamingType _ _ (Data c _ _)) -> ImportTypeWith tc [c]
>     Just _ -> errorAt p (nonDataType m tc)
>     Nothing -> errorAt p (undefinedEntity m tc)

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors.
\begin{verbatim}

> importUnifyData :: TCEnv -> TCEnv
> importUnifyData tcEnv =
>   fmap (setInfo (foldr (mergeData . snd) zeroFM (allImports tcEnv))) tcEnv
>   where setInfo tcs t = fromJust (lookupFM (origName t) tcs)
>         mergeData t tcs =
>           addToFM tc (maybe t (fromJust . merge t) (lookupFM tc tcs)) tcs
>           where tc = origName t

\end{verbatim}
Auxiliary functions:
\begin{verbatim}

> addType :: Import -> [Ident] -> [Ident]
> addType (Import _) tcs = tcs
> addType (ImportTypeWith tc _) tcs = tc : tcs
> addType (ImportTypeAll _) _ = internalError "types"

> addValue :: Import -> [Ident] -> [Ident]
> addValue (Import f) fs = f : fs
> addValue (ImportTypeWith _ cs) fs = cs ++ fs
> addValue (ImportTypeAll _) _ = internalError "values"

> addArity :: Import -> [Ident] -> [Ident]
> addArity (Import f) ids = f:ids
> addArity (ImportTypeWith _ cs) ids = cs ++ ids
> addArity (ImportTypeAll _) _ = internalError "arities"

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs = ConstructorType tc (map VariableType tvs)

\end{verbatim}
Error messages:
\begin{verbatim}

> undefinedEntity :: ModuleIdent -> Ident -> String
> undefinedEntity m x =
>   "Module " ++ moduleName m ++ " does not export " ++ name x

> undefinedType :: ModuleIdent -> Ident -> String
> undefinedType m tc =
>   "Module " ++ moduleName m ++ " does not export a type " ++ name tc

> undefinedDataConstr :: ModuleIdent -> Ident -> Ident -> String
> undefinedDataConstr m tc c =
>   name c ++ " is not a data constructor of type " ++ name tc

> nonDataType :: ModuleIdent -> Ident -> String
> nonDataType m tc = name tc ++ " is not a data type"

> importDataConstr :: ModuleIdent -> Ident -> String
> importDataConstr m c = "Explicit import for data constructor " ++ name c

\end{verbatim}
