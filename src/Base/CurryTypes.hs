{- |
    Module      :  $Header$
    Description :  Conversion of type representation
    Copyright   :  (c)         Wolfgang Lux
                   2011 - 2012 Björn Peemöller
                   2015        Jan Tikovsky
                   2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The functions 'toType', 'toTypes', and 'fromType' convert Curry type
   expressions into types and vice versa. The functions 'qualifyType' and
   'unqualifyType' add and remove module qualifiers in a type, respectively.

   When Curry type expression are converted with 'toType' or 'toTypes',
   type variables are assigned ascending indices in the order of their
   occurrence. It is possible to pass a list of additional type variables
   to both functions which are assigned indices before those variables
   occurring in the type. This allows preserving the order of type variables
   in the left hand side of a type declaration.
-}

module Base.CurryTypes
  ( toQualType, toQualTypes, toType, toTypes, fromQualType, fromType
  , toPredType, toPredSet, toPred, fromPredType, fromPredSet, fromPred
  , ppType, ppPred, ppTypeScheme
  ) where

import Data.List (nub)
import qualified Data.Map as Map (Map, fromList, lookup)
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Base.Pretty (Doc)
import qualified Curry.Syntax as CS
import Curry.Syntax.Pretty (ppConstraint, ppTypeExpr)

import Base.Expr
import Base.Messages (internalError)
import Base.Types

toQualType :: ModuleIdent -> [Ident] -> CS.TypeExpr -> Type
toQualType m tvs = qualifyType m . toType tvs

toQualTypes :: ModuleIdent -> [Ident] -> [CS.TypeExpr] -> [Type]
toQualTypes m tvs = map (qualifyType m) . toTypes tvs

toType :: [Ident] -> CS.TypeExpr -> Type
toType tvs ty = toType' (enumTypeVars tvs ty) ty []

toTypes :: [Ident] -> [CS.TypeExpr] -> [Type]
toTypes tvs tys = map ((flip $ toType' $ enumTypeVars tvs tys) []) tys

toPredType :: [Ident] -> CS.QualTypeExpr -> PredType
toPredType tvs (CS.QualTypeExpr cx ty) =
  PredType (toPredSet tvs cx) (toType tvs ty)

toPredSet :: [Ident] -> CS.Context -> PredSet
toPredSet tvs = Set.fromList . map (toPred tvs)

toPred :: [Ident] -> CS.Constraint -> Pred
toPred tvs (CS.Constraint qcls ty) = Pred qcls (toType tvs ty)

enumTypeVars :: Expr a => [Ident] -> a -> Map.Map Ident Int
enumTypeVars tvs ty = Map.fromList $ zip (tvs ++ tvs') [0..]
  where
    tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

toType' :: Map.Map Ident Int -> CS.TypeExpr -> [Type] -> Type
toType' _   (CS.ConstructorType tc) tys = applyType (TypeConstructor tc) tys
toType' tvs (CS.ApplyType  ty1 ty2) tys =
  toType' tvs ty1 (toType' tvs ty2 [] : tys)
toType' tvs (CS.VariableType    tv) tys = case Map.lookup tv tvs of
  Just tv' -> applyType (TypeVariable tv') tys
  Nothing  -> internalError "Base.CurryTypes.toType': unknown type variable"
toType' tvs (CS.TupleType      tys) tys'
  | null tys  = internalError "Base.CurryTypes.toType': zero-element tuple"
  | null tys' = tupleType $ map ((flip $ toType' tvs) []) tys
  | otherwise = internalError "Base.CurryTypes.toType': tuple type application"
toType' tvs (CS.ListType        ty) tys
  | null tys  = listType $ toType' tvs ty []
  | otherwise = internalError "Base.CurryTypes.toType': list type application"
toType' tvs (CS.ArrowType  ty1 ty2) tys
  | null tys = TypeArrow (toType' tvs ty1 []) (toType' tvs ty2 [])
  | otherwise = internalError "Base.CurryTypes.toType': arrow type application"
toType' tvs (CS.ParenType       ty) tys = toType' tvs ty tys

fromQualType :: ModuleIdent -> Type -> CS.TypeExpr
fromQualType m = fromType . unqualifyType m

fromType :: Type -> CS.TypeExpr
fromType ty = fromType' ty []

fromType' :: Type -> [CS.TypeExpr] -> CS.TypeExpr
fromType' (TypeConstructor    tc) tys
  | isQTupleId tc && qTupleArity tc == length tys = CS.TupleType tys
  | tc == qListId && length tys == 1              = CS.ListType (head tys)
  | otherwise
  = foldl CS.ApplyType (CS.ConstructorType tc) tys
fromType' (TypeApply     ty1 ty2) tys = fromType' ty1 (fromType ty2 : tys)
fromType' (TypeVariable       tv) tys =
  foldl CS.ApplyType (CS.VariableType tv') tys
  where
    tv' = if tv >= 0 then identSupply !! tv else mkIdent ('_' : show (-tv))
fromType' (TypeArrow     ty1 ty2) tys =
  foldl CS.ApplyType (CS.ArrowType (fromType ty1) (fromType ty2)) tys
fromType' (TypeConstrained tys _) tys' = fromType' (head tys) tys'
fromType' (TypeSkolem          k) tys =
  foldl CS.ApplyType (CS.VariableType $ mkIdent $ "_?" ++ show k) tys

fromPredType :: PredType -> CS.QualTypeExpr
fromPredType (PredType ps ty) = CS.QualTypeExpr (fromPredSet ps) (fromType ty)

fromPredSet :: PredSet -> CS.Context
fromPredSet = map fromPred . Set.toAscList

fromPred :: Pred -> CS.Constraint
fromPred (Pred qcls ty) = CS.Constraint qcls (fromType ty)

-- The following functions implement pretty-printing for types.
ppType :: ModuleIdent -> Type -> Doc
ppType m = ppTypeExpr 0 . fromQualType m

ppPred :: Pred -> Doc
ppPred = ppConstraint . fromPred

ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
ppTypeScheme m (ForAll _ ty) = ppType m ty
