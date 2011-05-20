\paragraph{Type constructors}
For all defined types the compiler must maintain kind information. At
present, Curry does not support type classes. Therefore its type
language is first order and the only information that must be recorded
is the arity of each type. For algebraic data types and renaming types
the compiler also records all data constructors belonging to that
type, for alias types the type expression to be expanded is saved. In
order to manage the import and export of types, the names of the
original definitions are also recorded. On import two types are
considered equal if their original names match.

The information for a data constructor comprises the number of
existentially quantified type variables and the list of the argument
types. Note that renaming type constructors have only one type
argument.

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type. When only some
constructors of a data type are hidden, those constructors are
replaced by underscores in the interface. Furthermore, if the
right-most constructors of a data type are hidden, they are not
exported at all in order to make the interface more stable against
changes which are private to the module.
\begin{verbatim}

> module Base.TypeConstructors
>   ( TCEnv, TypeInfo (..), tcArity, bindTypeInfo, lookupTC, qualLookupTC
>   , lookupTupleTC, tupleTCs, tupleData, initTCEnv
>   ) where

> import Control.Monad (mplus)

> import Curry.Base.Ident

> import Env.TopEnv
> import Utils ((++!))
> import Types

> data TypeInfo = DataType QualIdent Int [Maybe (Data [Type])]
>               | RenamingType QualIdent Int (Data Type)
>               | AliasType QualIdent Int Type
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _) = tc
>   merge (DataType tc n cs) (DataType tc' _ cs')
>     | tc == tc' = Just (DataType tc n (mergeData cs cs'))
>     where mergeData ds       []         = ds
>           mergeData []       ds         = ds
>           mergeData (d : ds) (d' : ds') = d `mplus` d' : mergeData ds ds'
>   merge (DataType tc n _) (RenamingType tc' _ nc)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (DataType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (RenamingType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (AliasType tc n ty) (AliasType tc' _ _)
>     | tc == tc' = Just (AliasType tc n ty)
>   merge _ _ = Nothing

> tcArity :: TypeInfo -> Int
> tcArity (DataType _ n _) = n
> tcArity (RenamingType _ n _) = n
> tcArity (AliasType _ n _) = n

\end{verbatim}
Types can only be defined on the top-level; no nested environments are
needed for them. Tuple types must be handled as a special case because
there is an infinite number of potential tuple types making it
impossible to insert them into the environment in advance.
\begin{verbatim}

> type TCEnv = TopEnv TypeInfo

> bindTypeInfo :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent
>              -> Ident -> [Ident] -> a -> TCEnv -> TCEnv
> bindTypeInfo f m tc tvs x
>   = bindTopEnv "Base.bindTypeInfo" tc t
>     . qualBindTopEnv "Base.bindTypeInfo" tc' t
>   where tc' = qualifyWith m tc
>         t = f tc' (length tvs) x

> lookupTC :: Ident -> TCEnv -> [TypeInfo]
> lookupTC tc tcEnv = lookupTopEnv tc tcEnv ++! lookupTupleTC tc

> qualLookupTC :: QualIdent -> TCEnv -> [TypeInfo]
> qualLookupTC tc tcEnv =
>   qualLookupTopEnv tc tcEnv ++! lookupTupleTC (unqualify tc)

> lookupTupleTC :: Ident -> [TypeInfo]
> lookupTupleTC tc
>   | isTupleId tc = [tupleTCs !! (tupleArity tc - 2)]
>   | otherwise = []

> tupleTCs :: [TypeInfo]
> tupleTCs = map typeInfo tupleData
>   where typeInfo (Data c _ tys) =
>           DataType (qualifyWith preludeMIdent c) (length tys)
>                    [Just (Data c 0 tys)]

> tupleData :: [Data [Type]]
> tupleData = [Data (tupleId n) 0 (take n tvs) | n <- [2 ..]]
>   where tvs = map typeVar [0 ..]

> initTCEnv :: TCEnv
> initTCEnv = foldr (uncurry predefTC) emptyTopEnv predefTypes
>   where predefTC (TypeConstructor tc tys) =
>           predefTopEnv (qualify (unqualify tc)) .
>             DataType tc (length tys) . map Just
>         predefTC _ = error "Base.initTCEnv.predefTC: no type constructor"

\end{verbatim}
