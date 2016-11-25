{- |
    Module      :  $Header$
    Description :  Type substitution
    Copyright   :  (c) 2003 Wolfgang Lux
                       2016 Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   This module implements substitutions on types.
-}

module Base.TypeSubst
  ( module Base.TypeSubst, idSubst, singleSubst, bindSubst, compose
  ) where

import           Data.List       (nub)
import           Data.Maybe      (fromMaybe)
import qualified Data.Set as Set (Set, map)

import Base.Subst
import Base.TopEnv
import Base.Types

import Env.Value (ValueInfo (..))

type TypeSubst = Subst Int Type

class SubstType a where
  subst :: TypeSubst -> a -> a

bindVar :: Int -> Type -> TypeSubst -> TypeSubst
bindVar tv ty = compose (bindSubst tv ty idSubst)

substVar :: TypeSubst -> Int -> Type
substVar = substVar' TypeVariable subst

instance (Ord a, SubstType a) => SubstType (Set.Set a) where
  subst sigma = Set.map (subst sigma)

instance SubstType a => SubstType [a] where
  subst sigma = map (subst sigma)

instance SubstType Type where
  subst sigma ty = subst' sigma ty []

subst' :: TypeSubst -> Type -> [Type] -> Type
subst' _     tc@(TypeConstructor   _) = foldl TypeApply tc
subst' sigma (TypeApply      ty1 ty2) = subst' sigma ty1 . (subst sigma ty2 :)
subst' sigma (TypeVariable        tv) = applyType (substVar sigma tv)
subst' sigma (TypeArrow      ty1 ty2) =
  foldl TypeApply (TypeArrow (subst sigma ty1) (subst sigma ty2))
subst' sigma (TypeConstrained tys tv) = case substVar sigma tv of
  TypeVariable tv' -> foldl TypeApply (TypeConstrained tys tv')
  ty               -> foldl TypeApply ty
subst' _     ts@(TypeSkolem        _) = foldl TypeApply ts
subst' sigma (TypeForall      tvs ty) =
  applyType (TypeForall tvs (subst sigma ty))

instance SubstType Pred where
  subst sigma (Pred qcls ty) = Pred qcls (subst sigma ty)

instance SubstType PredType where
  subst sigma (PredType ps ty) = PredType (subst sigma ps) (subst sigma ty)

instance SubstType TypeScheme where
  subst sigma (ForAll n ty) =
    ForAll n (subst (foldr unbindSubst sigma [0 .. n-1]) ty)

instance SubstType ExistTypeScheme where
  subst sigma (ForAllExist n n' ty) =
    ForAllExist n n' (subst (foldr unbindSubst sigma [0 .. n + n' - 1]) ty)

instance SubstType ValueInfo where
  subst _     dc@(DataConstructor  _ _ _ _) = dc
  subst _     nc@(NewtypeConstructor _ _ _) = nc
  subst theta (Value             v cm a ty) = Value v cm a (subst theta ty)
  subst theta (Label                l r ty) = Label l r (subst theta ty)

instance SubstType a => SubstType (TopEnv a) where
  subst = fmap . subst

-- The class method 'expandAliasType' expands all occurrences of a
-- type synonym in its second argument.

class ExpandAliasType a where
  expandAliasType :: [Type] -> a -> a

instance ExpandAliasType a => ExpandAliasType [a] where
  expandAliasType tys = map (expandAliasType tys)

instance (Ord a, ExpandAliasType a) => ExpandAliasType (Set.Set a) where
  expandAliasType tys = Set.map (expandAliasType tys)

instance ExpandAliasType Type where
  expandAliasType tys ty = expandAliasType' tys ty []

expandAliasType' :: [Type] -> Type -> [Type] -> Type
expandAliasType' _   tc@(TypeConstructor   _) = applyType tc
expandAliasType' tys (TypeApply      ty1 ty2) =
  expandAliasType' tys ty1 . (expandAliasType tys ty2 :)
expandAliasType' tys tv@(TypeVariable      n)
  | n >= 0    = applyType (tys !! n)
  | otherwise = applyType tv
expandAliasType' _   tc@(TypeConstrained _ _) = applyType tc
expandAliasType' tys (TypeArrow      ty1 ty2) =
  applyType (TypeArrow (expandAliasType tys ty1) (expandAliasType tys ty2))
expandAliasType' _   ts@(TypeSkolem        _) = applyType ts
expandAliasType' tys (TypeForall      tvs ty) =
  applyType (TypeForall tvs (expandAliasType tys ty))

instance ExpandAliasType Pred where
  expandAliasType tys (Pred qcls ty) = Pred qcls (expandAliasType tys ty)

instance ExpandAliasType PredType where
  expandAliasType tys (PredType ps ty) =
    PredType (expandAliasType tys ps) (expandAliasType tys ty)

-- After the expansion we have to reassign the type indices for all type
-- variables. Otherwise, expanding a type synonym like type 'Pair a b = (b,a)'
-- could break the invariant that the universally quantified type variables
-- are assigned indices in the order of their occurrence. This is handled by
-- the function 'normalize'. The function has a threshold parameter that allows
-- preserving the indices of type variables bound on the left hand side
-- of a type declaration and in the head of a type class declaration,
-- respectively.

normalize :: Int -> PredType -> PredType
normalize n ty = expandAliasType [TypeVariable (occur tv) | tv <- [0..]] ty
  where tvs = zip (nub (filter (>= n) (typeVars ty))) [n..]
        occur tv = fromMaybe tv (lookup tv tvs)

-- The function 'instanceType' computes an instance of a polymorphic type by
-- substituting the first type argument for all occurrences of the type
-- variable with index 0 in the second argument. The function carefully
-- assigns new indices to all other type variables of the second argument
-- so that they do not conflict with the type variables of the first argument.

instanceType :: ExpandAliasType a => Type -> a -> a
instanceType ty = expandAliasType (ty : map TypeVariable [n ..])
  where ForAll n _ = polyType ty
