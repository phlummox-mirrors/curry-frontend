
% $Id: TypeSubst.lhs,v 1.2 2004/02/08 22:14:01 wlux Exp $
%
% Copyright (c) 2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSubst.lhs}
\section{Type Substitutions}
This module implements substitutions on types.
\begin{verbatim}

> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module Base.TypeSubst
>   ( module Base.TypeSubst, idSubst, singleSubst, bindSubst, compose
>   ) where

> import Data.List (nub)
> import Data.Maybe (fromJust, isJust)

> import Base.Subst
> import Base.TopEnv
> import Base.Types

> import Env.Value (ValueInfo (..))

> type TypeSubst = Subst Int Type

> class SubstType a where
>   subst :: TypeSubst -> a -> a

> bindVar :: Int -> Type -> TypeSubst -> TypeSubst
> bindVar tv ty = compose (bindSubst tv ty idSubst)

> substVar :: TypeSubst -> Int -> Type
> substVar = substVar' TypeVariable subst

> instance SubstType Type where
>   subst sigma (TypeConstructor tc tys) =
>     TypeConstructor tc (map (subst sigma) tys)
>   subst sigma (TypeVariable        tv) = substVar sigma tv
>   subst sigma (TypeConstrained tys tv) = case substVar sigma tv of
>     TypeVariable tv' -> TypeConstrained tys tv'
>     ty -> ty
>   subst sigma (TypeArrow      ty1 ty2) =
>     TypeArrow (subst sigma ty1) (subst sigma ty2)
>   subst _     ts@(TypeSkolem        _) = ts
>   subst sigma (TypeRecord       fs rv)
>     | isJust rv = case substVar sigma (fromJust rv) of
>         TypeVariable tv -> TypeRecord fs' (Just tv)
>         ty              -> ty
>     | otherwise = TypeRecord fs' Nothing
>    where fs' = map (\ (l,ty) -> (l, subst sigma ty)) fs

> instance SubstType TypeScheme where
>   subst sigma (ForAll cx n ty) =
>     ForAll (substContext sigma cx) n 
>            (subst (foldr unbindSubst sigma [0..n-1]) ty)

> instance SubstType ExistTypeScheme where
>   subst sigma (ForAllExist cx n n' ty) =
>     ForAllExist (substContext sigma cx) n n' 
>                 (subst (foldr unbindSubst sigma [0..n+n'-1]) ty)

> instance SubstType ValueInfo where
>   subst _     dc@(DataConstructor  _ _ _) = dc
>   subst _     nc@(NewtypeConstructor _ _) = nc
>   subst theta (Value              v a ty) = Value v a (subst theta ty)
>   subst theta (Label              l r ty) = Label l r (subst theta ty)

> instance SubstType a => SubstType (TopEnv a) where
>   subst = fmap . subst

> instance SubstType Context where
>   subst = substContext

> instance (SubstType a, SubstType b) => SubstType (a, b) where
>   subst sigma (x, y) = (subst sigma x, subst sigma y)

> substContext :: TypeSubst -> Context -> Context
> substContext s cx = map (\(qid, ty) -> (qid, subst s ty)) cx  

\end{verbatim}
The function \texttt{expandAliasType} expands all occurrences of a
type synonym in a type. After the expansion we have to reassign the
type indices for all type variables. Otherwise, expanding a type
synonym like \verb|type Pair' a b = (b,a)| could break the invariant
that the universally quantified type variables are assigned indices in
the order of their occurrence. This is handled by the function
\texttt{normalize}.
\begin{verbatim}

> expandAliasType :: [Type] -> Type -> Type
> expandAliasType tys (TypeConstructor tc tys') =
>   TypeConstructor tc (map (expandAliasType tys) tys')
> expandAliasType tys (TypeVariable n)
>   | n >= 0    = tys !! n
>   | otherwise = TypeVariable n
> expandAliasType _   (TypeConstrained   tys n) = TypeConstrained tys n
> expandAliasType tys (TypeArrow       ty1 ty2) =
>   TypeArrow (expandAliasType tys ty1) (expandAliasType tys ty2)
> expandAliasType _   tsk@(TypeSkolem        _) = tsk
> expandAliasType tys (TypeRecord        fs rv)
>   | isJust rv =
>     let (TypeVariable tv) = expandAliasType tys $ TypeVariable $ fromJust rv
>     in  TypeRecord fs' (Just tv)
>   | otherwise =
>     TypeRecord fs' Nothing
>  where fs' = map (\ (l, ty) -> (l, expandAliasType tys ty)) fs

> normalize :: Type -> Type
> normalize ty = expandAliasType [TypeVariable (occur tv) | tv <- [0 ..]] ty
>   where tvs = zip (nub (filter (>= 0) (typeVars ty))) [0 ..]
>         occur tv = fromJust (lookup tv tvs)

\end{verbatim}
