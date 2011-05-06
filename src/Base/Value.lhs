\paragraph{Function and constructor types}
In order to test the type correctness of a module, the compiler needs
to determine the type of every data constructor, function,
variable, record and label in the module.
For the purpose of type checking there is no
need for distinguishing between variables and functions. For all objects
their original names and their types are saved. Functions also
contain arity information. Labels currently contain the name of their
defining record. On import two values
are considered equal if their original names match.
\begin{verbatim}

> module Base.Value
>   ( ValueEnv, ValueInfo (..), bindGlobalInfo, bindFun, rebindFun, bindLabel
>   , lookupValue, qualLookupValue, qualLookupCons, lookupTuple, tupleDCs
>   , initDCEnv ) where

> import Curry.Base.Ident

> import Base.TypeConstructors (TypeInfo (..), tupleTCs)
> import Env.TopEnv
> import Utils ((++!))
> import Types

> data ValueInfo = DataConstructor QualIdent ExistTypeScheme
>                | NewtypeConstructor QualIdent ExistTypeScheme
>                | Value QualIdent TypeScheme
>                | Label QualIdent QualIdent TypeScheme
>              -- Label <label> <record name> <type>
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor orgName _) = orgName
>   origName (NewtypeConstructor orgName _) = orgName
>   origName (Value orgName _) = orgName
>   origName (Label orgName _ _) = orgName
>
>   merge (Label l r ty) (Label l' r' _)
>     | l == l' && r == r' = Just (Label l r ty)
>     | otherwise = Nothing
>   merge x y
>     | origName x == origName y = Just x
>     | otherwise = Nothing


\end{verbatim}
Even though value declarations may be nested, the compiler uses only
flat environments for saving type information. This is possible
because all identifiers are renamed by the compiler. Here we need
special cases for handling tuple constructors.

\em{Note:} the function \texttt{qualLookupValue} has been extended to
allow the usage of the qualified list constructor \texttt{(Prelude.:)}.
\begin{verbatim}

> type ValueEnv = TopEnv ValueInfo

> bindGlobalInfo :: (QualIdent -> a -> ValueInfo) -> ModuleIdent -> Ident -> a
>                -> ValueEnv -> ValueEnv
> bindGlobalInfo f m c ty
>   = bindTopEnv "Base.bindGlobalInfo" c v
>     . qualBindTopEnv "Base.bindGlobalInfo" c' v
>   where c' = qualifyWith m c
>         v = f c' ty

> bindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> bindFun m f ty tyEnv
>   | uniqueId f == 0
>     = bindTopEnv "Base.bindFun" f v (qualBindTopEnv "Base.bindFun" f' v tyEnv)
>   | otherwise = bindTopEnv "Base.bindFun" f v tyEnv
>   where f' = qualifyWith m f
>         v = Value f' ty

> rebindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> rebindFun m f ty
>   | uniqueId f == 0 = rebindTopEnv f v . qualRebindTopEnv f' v
>   | otherwise = rebindTopEnv f v
>   where f' = qualifyWith m f
>         v = Value f' ty

> bindLabel :: Ident -> QualIdent -> TypeScheme -> ValueEnv -> ValueEnv
> bindLabel l r ty tyEnv = bindTopEnv "Base.bindLabel" l v tyEnv
>   where v  = Label (qualify l) r ty

> lookupValue :: Ident -> ValueEnv -> [ValueInfo]
> lookupValue x tyEnv = lookupTopEnv x tyEnv ++! lookupTuple x

> qualLookupValue :: QualIdent -> ValueEnv -> [ValueInfo]
> qualLookupValue x tyEnv =
>   qualLookupTopEnv x tyEnv
>   ++! qualLookupCons x tyEnv
>   ++! lookupTuple (unqualify x)

> qualLookupCons :: QualIdent -> ValueEnv -> [ValueInfo]
> qualLookupCons x tyEnv
>    | maybe False ((==) preludeMIdent) mmid && qid == consId
>       = qualLookupTopEnv (qualify qid) tyEnv
>    | otherwise = []
>  where (mmid, qid) = (qualidMod x, qualidId x)

> lookupTuple :: Ident -> [ValueInfo]
> lookupTuple c
>   | isTupleId c = [tupleDCs !! (tupleArity c - 2)]
>   | otherwise = []

TODO: Match other patterns?

> tupleDCs :: [ValueInfo]
> tupleDCs = map dataInfo tupleTCs
>   where dataInfo (DataType tc _ [Just (Data _ _ tys)]) =
>           DataConstructor (qualUnqualify preludeMIdent tc)
>                           (ForAllExist (length tys) 0
>                                        (foldr TypeArrow (tupleType tys) tys))
>         dataInfo _ = error "Base.tupleDCs.dataInfo: no pattern match"

> initDCEnv :: ValueEnv
> initDCEnv =
>   foldr (uncurry predefDC) emptyTopEnv
>         [(c,constrType (polyType ty) n' tys)
>         | (ty,cs) <- predefTypes, Data c n' tys <- cs]
>   where predefDC c ty = predefTopEnv c' (DataConstructor c' ty)
>           where c' = qualify c
>         constrType (ForAll n ty) n' = ForAllExist n n' . foldr TypeArrow ty

\end{verbatim}
