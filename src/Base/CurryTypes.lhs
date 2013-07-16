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

> module Base.CurryTypes
>  ( toQualType, toQualTypes, toType, toTypes, fromQualType, fromType
>  , toTypeAndGetMap, toConstrType, toConstrTypes, fromContext
>  , fromType', fromQualType'
>  ) where

> import Data.List (nub)
> import Data.Maybe (fromJust)
> import qualified Data.Map as Map (Map, fromList, lookup)

> import Curry.Base.Ident
> import qualified Curry.Syntax as CS

> import Base.Expr
> import Base.Messages (internalError)
> import Base.Types as BT

> toQualType :: ModuleIdent -> [Ident] -> CS.TypeExpr -> Type
> toQualType m tvs = qualifyType m . toType tvs

> toQualTypes :: ModuleIdent -> [Ident] -> [CS.TypeExpr] -> [Type]
> toQualTypes m tvs = map (qualifyType m) . toTypes tvs

> toTypeAndGetMap :: [Ident] -> CS.TypeExpr -> (Type, Map.Map Ident Int)
> toTypeAndGetMap tvs ty = (toType' theMap ty, theMap)
>   where newInTy = [tv | tv <- nub (fv ty), tv `notElem` tvs]
>         theMap = Map.fromList $ zip (tvs ++ newInTy) [0 ..]

> toType :: [Ident] -> CS.TypeExpr -> Type
> toType tvs ty = fst $ toTypeAndGetMap tvs ty 

> toTypesAndGetMap :: [Ident] -> [CS.TypeExpr] -> ([Type], Map.Map Ident Int)
> toTypesAndGetMap tvs tys = (map (toType' theMap) tys, theMap)
>   where newInTys = [tv | tv <- nub (concatMap fv tys), tv `notElem` tvs]
>         theMap = Map.fromList $ zip (tvs ++ newInTys) [0 ..]

> toTypes :: [Ident] -> [CS.TypeExpr] -> [Type]
> toTypes tvs tys = fst $ toTypesAndGetMap tvs tys

> toConstrType :: [Ident] -> (CS.Context, CS.TypeExpr) -> (Context, Type)
> toConstrType tvs (cx, ty) = 
>   let (theType, theMap) = toTypeAndGetMap tvs ty
>       translatedContext = translateContext theMap cx
>   in (translatedContext, theType)

> toConstrTypes :: [Ident] -> [(CS.Context, CS.TypeExpr)] -> [(Context, Type)]
> toConstrTypes tvs tys = 
>   let (theTypes, theMap) = toTypesAndGetMap tvs (map snd tys)
>       contexts = map (translateContext theMap . fst) tys
>   in zip contexts theTypes  

> translateContext :: Map.Map Ident Int -> CS.Context -> BT.Context
> translateContext theMap (CS.Context elems) 
>   -- TODO: translate also texps!
>   = map (\(CS.ContextElem qid id0 _texps) -> 
>          (qid, TypeVariable (fromJust $ Map.lookup id0 theMap)))
>         elems

> toType' :: Map.Map Ident Int -> CS.TypeExpr -> Type
> toType' tvs (CS.ConstructorType tc tys)
>   = TypeConstructor tc (map (toType' tvs) tys)
> toType' tvs (CS.SpecialConstructorType (CS.QualTC tc) tys)
>   = toType' tvs (CS.ConstructorType tc tys)
> toType' tvs (CS.SpecialConstructorType CS.UnitTC tys)
>   = toType' tvs (CS.TupleType tys)
> toType' tvs (CS.SpecialConstructorType (CS.TupleTC _n) tys)
>   = toType' tvs (CS.TupleType tys)
> toType' tvs (CS.SpecialConstructorType CS.ListTC [ty])
>   = toType' tvs (CS.ListType ty)
> toType' _tvs (CS.SpecialConstructorType CS.ListTC _)
>   = internalError "toType': list"
> toType' tvs (CS.SpecialConstructorType CS.ArrowTC [ty1, ty2])
>   = toType' tvs (CS.ArrowType ty1 ty2)  
> toType' _tvs (CS.SpecialConstructorType CS.ArrowTC _)
>   = internalError "toType': arrow"
> toType' tvs (CS.VariableType        tv) = case Map.lookup tv tvs of
>   Just tv' -> TypeVariable tv'
>   Nothing  -> internalError $ "Base.CurryTypes.toType': " ++ show tv
> toType' tvs (CS.TupleType          tys)
>   | null tys  = TypeConstructor (qualify unitId) []
>   | otherwise = TypeConstructor (qualify $ tupleId $ length tys') tys'
>   where tys' = map (toType' tvs) tys
> toType' tvs (CS.ListType            ty)
>   = TypeConstructor (qualify listId) [toType' tvs ty]
> toType' tvs (CS.ArrowType      ty1 ty2)
>   = TypeArrow (toType' tvs ty1) (toType' tvs ty2)
> toType' tvs (CS.RecordType      fs rty)
>   = TypeRecord fs' rty'
>   where
>     fs'  = concatMap (\ (ls, ty) -> map (\ l -> (l, toType' tvs ty)) ls) fs
>     rty' = case rty of
>       Nothing -> Nothing
>       Just ty -> case toType' tvs ty of
>         TypeVariable tv -> Just tv
>         _ -> internalError $ "Base.CurryTypes.toType' " ++ show ty

> fromQualType :: ModuleIdent -> Type -> CS.TypeExpr
> fromQualType = fromQualType' identSupply

> fromQualType' :: [Ident] -> ModuleIdent -> Type -> CS.TypeExpr
> fromQualType' supply m = fromType' supply . unqualifyType m

> -- |converts a "Type" into a "TypeExpr"
> fromType :: Type -> CS.TypeExpr
> fromType = fromType' identSupply

> -- |converts a "Type" into a "TypeExpr", using the given identifier supply. 
> -- each variable @i@ is replaced by @supply !! i@  
> fromType' :: [Ident] -> Type -> CS.TypeExpr
> fromType' supply (TypeConstructor tc tys)
>   | isTupleId c                    = CS.TupleType tys'
>   | c == unitId && null tys        = CS.TupleType []
>   | c == listId && length tys == 1 = CS.ListType (head tys')
>   | otherwise                      = CS.ConstructorType tc tys'
>   where c    = unqualify tc
>         tys' = map (fromType' supply) tys
> fromType' supply (TypeVariable tv)         = CS.VariableType
>    (if tv >= 0 then supply !! tv else mkIdent ('_' : show (-tv)))
> fromType' supply (TypeConstrained tys _)   = fromType' supply (head tys)
> fromType' supply (TypeArrow     ty1 ty2)   =
>   CS.ArrowType (fromType' supply ty1) (fromType' supply ty2)
> fromType' _supply (TypeSkolem          k)   =
>   CS.VariableType $ mkIdent $ "_?" ++ show k
> fromType' supply (TypeRecord     fs rty)   = CS.RecordType
>   (map (\ (l, ty) -> ([l], fromType' supply ty)) fs)
>   ((fromType' supply . TypeVariable) `fmap` rty)

> fromContext :: BT.Context -> CS.Context
> fromContext cx = CS.Context $ map fromCx cx
>   where
>   -- assumes that context elements are in head normal form!
>   fromCx :: (QualIdent, Type) -> CS.ContextElem
>   fromCx (qid, TypeVariable i) = CS.ContextElem qid (supply i) [] 
>   fromCx _ = internalError "fromContext"
>   supply i | i >= 0 = identSupply !! i
>            | otherwise = mkIdent ('_' : show (-i))

