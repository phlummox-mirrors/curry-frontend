\paragraph{Types}
The functions \texttt{toType}, \texttt{toTypes}, and \texttt{fromType}
convert Curry type expressions into types and vice versa. The
functions \texttt{qualifyType} and \texttt{unqualifyType} add and
remove module qualifiers in a type, respectively.

When Curry type expression are converted with \texttt{toType} or
\texttt{toTypes}, type variables are assigned ascending indices in the
order of their occurrence. It is possible to pass a list of additional
type variables to both functions which are assigned indices before
those variables occurring in the type. This allows preserving the
order of type variables in the left hand side of a type declaration.
\begin{verbatim}

> module Base.Types
>  ( toQualType, toQualTypes, toType, toTypes, toType', fromQualType, fromType
>  ) where

> import Data.List (nub)
> import qualified Data.Map as Map (Map, fromList, lookup)

> import Curry.Base.Ident
> import qualified Curry.Syntax as CS

> import Base.Expr
> import Messages (internalError)
> import Types

> toQualType :: ModuleIdent -> [Ident] -> CS.TypeExpr -> Type
> toQualType m tvs = qualifyType m . toType tvs

> toQualTypes :: ModuleIdent -> [Ident] -> [CS.TypeExpr] -> [Type]
> toQualTypes m tvs = map (qualifyType m) . toTypes tvs

> toType :: [Ident] -> CS.TypeExpr -> Type
> toType tvs ty = toType' (Map.fromList (zip (tvs ++ tvs') [0 ..])) ty
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> toTypes :: [Ident] -> [CS.TypeExpr] -> [Type]
> toTypes tvs tys = map (toType' (Map.fromList (zip (tvs ++ tvs') [0 ..]))) tys
>   where tvs' = [tv | tv <- nub (concatMap fv tys), tv `notElem` tvs]

> toType' :: Map.Map Ident Int -> CS.TypeExpr -> Type
> toType' tvs (CS.ConstructorType tc tys) =
>   TypeConstructor tc (map (toType' tvs) tys)
> toType' tvs (CS.VariableType tv) =
>   maybe (internalError ("toType " ++ show tv)) TypeVariable (Map.lookup tv tvs)
> toType' tvs (CS.TupleType tys)
>   | null tys = TypeConstructor (qualify unitId) []
>   | otherwise = TypeConstructor (qualify (tupleId (length tys'))) tys'
>   where tys' = map (toType' tvs) tys
> toType' tvs (CS.ListType ty) = TypeConstructor (qualify listId) [toType' tvs ty]
> toType' tvs (CS.ArrowType ty1 ty2) =
>   TypeArrow (toType' tvs ty1) (toType' tvs ty2)
> toType' tvs (CS.RecordType fs rty) =
>   TypeRecord (concatMap (\ (ls, ty) -> map (\ l -> (l, toType' tvs ty)) ls) fs)
>              (maybe Nothing
>                 (\ ty -> case toType' tvs ty of
>                           TypeVariable tv -> Just tv
>                           _ -> internalError ("toType " ++ show ty))
>                 rty)

> fromQualType :: ModuleIdent -> Type -> CS.TypeExpr
> fromQualType m = fromType . unqualifyType m

> fromType :: Type -> CS.TypeExpr
> fromType (TypeConstructor tc tys)
>   | isTupleId c = CS.TupleType tys'
>   | c == listId && length tys == 1 = CS.ListType (head tys')
>   | c == unitId && null tys = CS.TupleType []
>   | otherwise = CS.ConstructorType tc tys'
>   where c = unqualify tc
>         tys' = map fromType tys
> fromType (TypeVariable tv) =
>   CS.VariableType (if tv >= 0 then identSupply !! tv
>                            else mkIdent ('_' : show (-tv)))
> fromType (TypeConstrained tys _) = fromType (head tys)
> fromType (TypeArrow ty1 ty2) = CS.ArrowType (fromType ty1) (fromType ty2)
> fromType (TypeSkolem k) = CS.VariableType (mkIdent ("_?" ++ show k))
> fromType (TypeRecord fs rty) =
>   CS.RecordType (map (\ (l, ty) -> ([l], fromType ty)) fs)
>              (maybe Nothing (Just . fromType . TypeVariable) rty)
