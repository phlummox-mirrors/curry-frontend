{- |
    Module      :  $Header$
    Description :  Conversion of type representation
    Copyright   :  (c)         Wolfgang Lux
                   2011 - 2012 Björn Peemöller
                   2015        Jan Tikovsky
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
 ( toQualType, toQualTypes, toType, toTypes, fromQualType, fromType,
   ppType, ppTypeScheme
 ) where

import Data.List (nub)
import qualified Data.Map as Map (Map, fromList, lookup)

import Curry.Base.Ident
import Curry.Base.Pretty (Doc)
import qualified Curry.Syntax as CS
import Curry.Syntax.Pretty (ppTypeExpr)

import Base.Expr
import Base.Messages (internalError)
import Base.Types

toQualType :: ModuleIdent -> [Ident] -> CS.TypeExpr -> Type
toQualType m tvs = qualifyType m . toType tvs

toQualTypes :: ModuleIdent -> [Ident] -> [CS.TypeExpr] -> [Type]
toQualTypes m tvs = map (qualifyType m) . toTypes tvs

toType :: [Ident] -> CS.TypeExpr -> Type
toType tvs ty = toType' (Map.fromList $ zip (tvs ++ newInTy) [0 ..]) ty
  where newInTy = [tv | tv <- nub (fv ty), tv `notElem` tvs]

toTypes :: [Ident] -> [CS.TypeExpr] -> [Type]
toTypes tvs tys = map
   (toType' (Map.fromList $ zip (tvs ++ newInTys) [0 ..])) tys
  where newInTys = [tv | tv <- nub (concatMap fv tys), tv `notElem` tvs]

toType' :: Map.Map Ident Int -> CS.TypeExpr -> Type
toType' tvs (CS.ConstructorType tc tys)
  = TypeConstructor tc (map (toType' tvs) tys)
toType' tvs (CS.VariableType        tv) = case Map.lookup tv tvs of
  Just tv' -> TypeVariable tv'
  Nothing  -> internalError $ "Base.CurryTypes.toType': " ++ show tv
toType' tvs (CS.TupleType          tys)
  | null tys  = TypeConstructor (qualify unitId) []
  | otherwise = TypeConstructor (qualify $ tupleId $ length tys') tys'
  where tys' = map (toType' tvs) tys
toType' tvs (CS.ListType            ty)
  = TypeConstructor (qualify listId) [toType' tvs ty]
toType' tvs (CS.ArrowType      ty1 ty2)
  = TypeArrow (toType' tvs ty1) (toType' tvs ty2)
toType' tvs (CS.ParenType           ty) = toType' tvs ty

fromQualType :: ModuleIdent -> Type -> CS.TypeExpr
fromQualType m = fromType . unqualifyType m

fromType :: Type -> CS.TypeExpr
fromType (TypeConstructor tc tys)
  | isTupleId c                    = CS.TupleType tys'
  | c == unitId && null tys        = CS.TupleType []
  | c == listId && length tys == 1 = CS.ListType (head tys')
  | otherwise                      = CS.ConstructorType tc tys'
  where c    = unqualify tc
        tys' = map fromType tys
fromType (TypeVariable tv)         = CS.VariableType
   (if tv >= 0 then identSupply !! tv else mkIdent ('_' : show (-tv)))
fromType (TypeConstrained tys _)   = fromType (head tys)
fromType (TypeArrow     ty1 ty2)   =
  CS.ArrowType (fromType ty1) (fromType ty2)
fromType (TypeSkolem          k)   =
  CS.VariableType $ mkIdent $ "_?" ++ show k

-- The following functions implement pretty-printing for types.
ppType :: ModuleIdent -> Type -> Doc
ppType m = ppTypeExpr 0 . fromQualType m

ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
ppTypeScheme m (ForAll _ ty) = ppType m ty
