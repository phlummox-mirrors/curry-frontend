{- |
    Module      :  $Header$
    Description :  Type computation of Curry expressions
    Copyright   :  (c) 2003 - 2006 Wolfgang Lux
                       2014 - 2015 Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

-}

module Base.Typing (Typeable (..)) where

import Control.Monad
import qualified Control.Monad.State as S (State, evalState, gets, modify)

import Curry.Base.Ident
import Curry.Syntax

import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.TypeSubst
import Base.Utils (foldr2)

import Env.Value ( ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

-- During the transformation of Curry source code into the intermediate
-- language, the compiler has to recompute the types of expressions. This
-- is simpler than type checking because the types of all variables are
-- known. Yet, the compiler still must handle functions and constructors
-- with polymorphic types and instantiate their type schemes using fresh
-- type variables. Since all types computed by 'typeOf' are monomorphic,
-- we can use type variables with non-negative offsets for the instantiation
-- of type schemes here without risk of name conflicts.
-- Using non-negative offsets also makes it easy to distinguish these
-- fresh variables from free type variables introduced during type
-- inference, which must be regarded as constants here.

-- However, using non-negative offsets for fresh type variables gives
-- rise to two problems when those types are entered back into the type
-- environment, e.g., while introducing auxiliary variables during
-- desugaring. The first is that those type variables now appear to be
-- universally quantified variables, but with indices greater than the
-- number of quantified type variables (To be precise, this can
-- happen only for auxiliary variables, which have monomorphic types,
-- whereas auxiliary functions will be assigned polymorphic types and
-- these type variables will be properly quantified. However, in this
-- case the assigned types may be too general.).
-- This results in an internal error (Prelude.!!: index too large)
-- whenever such a type is instantiated.
-- The second problem is that there may be inadvertent name captures
-- because computeType always uses indices starting at 0 for the fresh
-- type variables. In order to avoid these problems, 'computeType' renames
-- all type variables with non-negative offsets after the final type has
-- been computed, using negative indices below the one with the smallest
-- value occurring in the type environment. Computing the minimum index
-- of all type variables in the type environment seems prohibitively
-- inefficient. However, recall that, thanks to laziness, the minimum is
-- computed only when the final type contains any type variables with
-- non-negative indices. This happens, for instance, 36 times while
-- compiling the prelude (for 159 evaluated applications of 'typeOf') and
-- only twice while compiling the standard IO module (for 21 applications
-- of 'typeOf') (These numbers were obtained for version 0.9.9.).

-- A careful reader will note that inadvertent name captures are still
-- possible if one computes the types of two or more auxiliary variables
-- before actually entering their types into the environment. Therefore,
-- make sure that you enter the types of these auxiliary variables
-- immediately into the type environment, unless you are sure that those
-- types cannot contain fresh type variables. One such case are the free
-- variables of a goal.

-- TODO: In the long run, this module should be made obsolete by adding
-- attributes to the abstract syntax tree -- e.g., along the lines of
-- Chap.~6 in~\cite{PeytonJonesLester92:Book} -- and returning an
-- abstract syntax tree attributed with type information together with
-- the type environment from type inference. This also would allow
-- getting rid of the identifiers in the representation of integer
-- literals, which are used in order to implement overloading of
-- integer constants.

-- TODO: When computing the type of an expression with a type signature
-- make use of the annotation instead of recomputing its type. In order
-- to do this, we must either ensure that the types are properly
-- qualified and expanded or we need access to the type constructor
-- environment.

data TcState = TcState
  { valueEnv  :: ValueEnv
  , typeSubst :: TypeSubst
  , nextId    :: Int
  }

type TCM = S.State TcState

getValueEnv :: TCM ValueEnv
getValueEnv = S.gets valueEnv

getTypeSubst :: TCM TypeSubst
getTypeSubst = S.gets typeSubst

modifyTypeSubst :: (TypeSubst -> TypeSubst) -> TCM ()
modifyTypeSubst f = S.modify $ \s -> s { typeSubst = f $ typeSubst s }

getNextId :: TCM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \ s -> s { nextId = succ nid }
  return nid

run :: TCM a -> ValueEnv -> a
run m tyEnv = S.evalState m initState
  where initState = TcState tyEnv idSubst 0

class Typeable a where
  typeOf :: ValueEnv -> a -> Type

instance Typeable Type where
  typeOf _ ty = ty

instance Typeable Ident where
  typeOf = computeType identType

instance Typeable Pattern where
  typeOf = computeType argType

instance Typeable Expression where
  typeOf = computeType exprType

instance Typeable Rhs where
  typeOf = computeType rhsType

computeType :: (a -> TCM Type) -> ValueEnv -> a -> Type
computeType f tyEnv x = normalize (run doComputeType tyEnv)
  where
    doComputeType = do
      ty    <- f x
      theta <- getTypeSubst
      return (fixTypeVars tyEnv (subst theta ty))

fixTypeVars :: ValueEnv -> Type -> Type
fixTypeVars tyEnv ty = subst (foldr2 bindSubst idSubst tvs tvs') ty
  where tvs = filter (>= 0) (typeVars ty)
        tvs' = map TypeVariable [n - 1,n - 2 ..]
        n = minimum (0 : concatMap typeVars tys)
        tys = [ty1 | (_,Value _ _ (ForAll _ ty1)) <- localBindings tyEnv]

identType :: Ident -> TCM Type
identType x = do
  tyEnv <- getValueEnv
  instUniv (varType x tyEnv)

litType :: Literal -> TCM Type
litType (Char _ _)   = return charType
litType (Int v _)    = identType v
litType (Float _ _)  = return floatType
litType (String _ _) = return stringType

argType :: Pattern -> TCM Type
argType (LiteralPattern l) = litType l
argType (NegativePattern _ l) = litType l
argType (VariablePattern v) = identType v
argType (ConstructorPattern c ts) = do
  tyEnv <- getValueEnv
  ty    <- instUnivExist (constrType c tyEnv)
  tys   <- mapM argType ts
  unifyList (init (flatten ty)) tys
  return (last (flatten ty))
  where flatten (TypeArrow ty1 ty2) = ty1 : flatten ty2
        flatten ty = [ty]
argType (InfixPattern t1 op t2) =
  argType (ConstructorPattern op [t1,t2])
argType (ParenPattern t) = argType t
argType (RecordPattern c fs) = do
  tyEnv <- getValueEnv
  ty    <- liftM arrowBase $ instUnivExist $ constrType c tyEnv
  mapM_ (fieldType argType ty) fs
  return ty
argType (TuplePattern _ ts)
  | null ts = return unitType
  | otherwise = liftM tupleType $ mapM argType ts
argType (ListPattern _ ts) = freshTypeVar >>= flip elemType ts
  where elemType ty [] = return (listType ty)
        elemType ty (t:ts1) =
          argType t >>= unify ty >> elemType ty ts1
argType (AsPattern v _) = argType (VariablePattern v)
argType (LazyPattern _ t) = argType t
argType (FunctionPattern f ts) = do
  tyEnv <- getValueEnv
  ty    <- instUniv (funType f tyEnv)
  tys   <- mapM argType ts
  unifyList (init (flatten ty)) tys
  return (last (flatten ty))
  where flatten (TypeArrow ty1 ty2) = ty1 : flatten ty2
        flatten ty = [ty]
argType (InfixFuncPattern t1 op t2) = argType (FunctionPattern op [t1,t2])

exprType :: Expression -> TCM Type
exprType (Literal l) = litType l
exprType (Variable v) = do
  tyEnv <- getValueEnv
  instUniv (funType v tyEnv)
exprType (Constructor c) = do
  tyEnv <- getValueEnv
  instUnivExist (constrType c tyEnv)
exprType (Typed e _) = exprType e
exprType (Paren e) = exprType e
exprType (Record c fs) = do
  tyEnv <- getValueEnv
  ty    <- liftM arrowBase $ instUnivExist $ constrType c tyEnv
  mapM_ (fieldType exprType ty) fs
  return ty
exprType (RecordUpdate e fs) = do
  ty <- exprType e
  mapM_ (fieldType exprType ty) fs
  return ty
exprType (Tuple _ es)
  | null es   = return unitType
  | otherwise = liftM tupleType $ mapM exprType es
exprType (List _ es) = freshTypeVar >>= flip elemType es
  where elemType ty []      = return (listType ty)
        elemType ty (e:es1) = exprType e >>= unify ty >> elemType ty es1
exprType (ListCompr _ e _) = liftM listType $ exprType e
exprType (EnumFrom _) = return (listType intType)
exprType (EnumFromThen _ _) = return (listType intType)
exprType (EnumFromTo _ _) = return (listType intType)
exprType (EnumFromThenTo _ _ _) = return (listType intType)
exprType (UnaryMinus _ e) = exprType e
exprType (Apply e1 e2) = do
  (ty1,ty2) <- exprType e1 >>= unifyArrow
  exprType e2 >>= unify ty1
  return ty2
exprType (InfixApply e1 op e2) = do
  (ty1,ty2,ty3) <- exprType (infixOp op) >>= unifyArrow2
  exprType e1 >>= unify ty1
  exprType e2 >>= unify ty2
  return ty3
exprType (LeftSection e op) = do
  (ty1,ty2,ty3) <- exprType (infixOp op) >>= unifyArrow2
  exprType e >>= unify ty1
  return (TypeArrow ty2 ty3)
exprType (RightSection op e) = do
  (ty1,ty2,ty3) <- exprType (infixOp op) >>= unifyArrow2
  exprType e >>= unify ty2
  return (TypeArrow ty1 ty3)
exprType (Lambda _ args e) = do
  tys <- mapM argType args
  ty  <- exprType e
  return (foldr TypeArrow ty tys)
exprType (Let _ e) = exprType e
exprType (Do _ e) = exprType e
exprType (IfThenElse _ e1 e2 e3) = do
  exprType e1 >>= unify boolType
  ty2 <- exprType e2
  ty3 <- exprType e3
  unify ty2 ty3
  return ty3
exprType (Case _ _ _ alts) = freshTypeVar >>= flip altType alts
  where altType ty [] = return ty
        altType ty (Alt _ _ rhs:alts1) =
          rhsType rhs >>= unify ty >> altType ty alts1

rhsType :: Rhs -> TCM Type
rhsType (SimpleRhs _ e _) = exprType e
rhsType (GuardedRhs es _) = freshTypeVar >>= flip condExprType es
  where condExprType ty [] = return ty
        condExprType ty (CondExpr _ _ e:es1) =
          exprType e >>= unify ty >> condExprType ty es1

fieldType :: (a -> TCM Type) -> Type -> Field a -> TCM Type
fieldType tcheck ty (Field _ l x) = do
  tyEnv <- getValueEnv
  TypeArrow ty1 ty2 <- instUniv (labelType l tyEnv)
  unify ty ty1
  lty <- tcheck x
  unify ty2 lty
  return lty

-- In order to avoid name conflicts with non-generalized type variables
-- in a type we instantiate quantified type variables using non-negative
-- offsets here.

freshTypeVar :: TCM Type
freshTypeVar = TypeVariable `liftM` getNextId

instType :: Int -> Type -> TCM Type
instType n ty = do
  tys <- replicateM n freshTypeVar
  return (expandAliasType tys ty)

instUniv :: TypeScheme -> TCM Type
instUniv (ForAll n ty) = instType n ty

instUnivExist :: ExistTypeScheme -> TCM Type
instUnivExist (ForAllExist n n' ty) = instType (n + n') ty

-- When unifying two types, the non-generalized variables, i.e.,
-- variables with negative offsets, must not be substituted. Otherwise,
-- the unification algorithm is identical to the one used by the type
-- checker.

unify :: Type -> Type -> TCM ()
unify ty1 ty2 = do
  theta <- getTypeSubst
  let ty1' = subst theta ty1
      ty2' = subst theta ty2
  modifyTypeSubst $ unifyTypes ty1' ty2'

unifyList :: [Type] -> [Type] -> TCM ()
unifyList tys1 tys2 = zipWithM_ unify tys1 tys2

unifyArrow :: Type -> TCM (Type,Type)
unifyArrow ty = do
  theta <- getTypeSubst
  case subst theta ty of
    TypeVariable tv
      | tv >= 0 -> do
        ty1 <- freshTypeVar
        ty2 <- freshTypeVar
        modifyTypeSubst (bindVar tv (TypeArrow ty1 ty2))
        return (ty1,ty2)
    TypeArrow ty1 ty2 -> return (ty1,ty2)
    ty' -> internalError ("Base.Typing.unifyArrow (" ++ show ty' ++ ")")

unifyArrow2 :: Type -> TCM (Type,Type,Type)
unifyArrow2 ty = do
  (ty1,ty2)   <- unifyArrow ty
  (ty21,ty22) <- unifyArrow ty2
  return (ty1,ty21,ty22)

unifyTypes :: Type -> Type -> TypeSubst -> TypeSubst
unifyTypes (TypeVariable tv1) (TypeVariable tv2) theta
  | tv1 == tv2 = theta
unifyTypes (TypeVariable tv) ty theta
  | tv >= 0 = bindVar tv ty theta
unifyTypes ty (TypeVariable tv) theta
  | tv >= 0 = bindVar tv ty theta
unifyTypes (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2) theta
  | tc1 == tc2 = foldr2 unifyTypes theta tys1 tys2
unifyTypes (TypeConstrained _ tv1) (TypeConstrained _ tv2) theta
  | tv1 == tv2 = theta
unifyTypes (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) theta =
  unifyTypes ty11 ty21 (unifyTypes ty12 ty22 theta)
unifyTypes (TypeSkolem k1) (TypeSkolem k2) theta
  | k1 == k2 = theta
unifyTypes ty1 ty2 _ = internalError $
  "Base.Typing.unify: (" ++ show ty1 ++ ") (" ++ show ty2 ++ ")"

-- The functions 'constrType', 'varType', and 'funType' are used for computing
-- the type of constructors, pattern variables, and variables.

-- TODO: These functions should be shared with the type checker.

constrType :: QualIdent -> ValueEnv -> ExistTypeScheme
constrType c tyEnv = case qualLookupValue c tyEnv of
  [DataConstructor  _ _ _ sigma] -> sigma
  [NewtypeConstructor _ _ sigma] -> sigma
  _ -> internalError $ "Base.Typing.constrType: " ++ show c

varType :: Ident -> ValueEnv -> TypeScheme
varType v tyEnv = case lookupValue v tyEnv of
  [Value _ _ sigma] -> sigma
  [Label _ _ sigma] -> sigma
  _ -> internalError $ "Base.Typing.varType: " ++ show v

funType :: QualIdent -> ValueEnv -> TypeScheme
funType f tyEnv = case qualLookupValue f tyEnv of
  [Value _ _ sigma] -> sigma
  [Label _ _ sigma] -> sigma
  _ -> internalError $ "Base.Typing.funType: " ++ show f

labelType :: QualIdent -> ValueEnv -> TypeScheme
labelType l tyEnv = case qualLookupValue l tyEnv of
  [Label _ _ sigma] -> sigma
  _ -> internalError $ "Base.Typing.labelType: " ++ show l
