{- |
    Module      :  $Header$
    Description :  Type computation of Curry expressions
    Copyright   :  (c) 2003 - 2006 Wolfgang Lux
                       2014        Jan Tikovsky
    License     :  OtherLicense

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

import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

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
  , tyConsEnv :: TCEnv
  , typeSubst :: TypeSubst
  , nextId    :: Int
  }

type TCM = S.State TcState

getTyConsEnv :: TCM TCEnv
getTyConsEnv = S.gets tyConsEnv

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

run :: TCM a -> ValueEnv -> TCEnv -> a
run m tyEnv tcEnv = S.evalState m initState
  where initState = TcState tyEnv tcEnv idSubst 0

class Typeable a where
  typeOf :: ValueEnv -> TCEnv -> a -> Type

instance Typeable Ident where
  typeOf = computeType identType

instance Typeable Pattern where
  typeOf = computeType argType

instance Typeable Expression where
  typeOf = computeType exprType

instance Typeable Rhs where
  typeOf = computeType rhsType

computeType :: (a -> TCM Type) -> ValueEnv -> TCEnv -> a -> Type
computeType f tyEnv tcEnv x = normalize (run doComputeType tyEnv tcEnv)
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
        tys = [ty1 | (_,Value _ _ (ForAll _ _ ty1) _) <- localBindings tyEnv]

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
argType tyEnv (InfixFuncPattern t1 op t2) =
  argType tyEnv (FunctionPattern op [t1,t2])
argType _ (RecordPattern fs _) = do
  recInfo <- getFieldIdent fs >>= getRecordInfo
  case recInfo of
    [AliasType qi n rty@(TypeRecord _)] -> do
      (TypeRecord fts', tys) <- instType' n rty
      fts   <- mapM fieldPattType fs
      theta <- getTypeSubst
      let theta' = foldr (unifyTypedLabels fts') theta fts
      modifyTypeSubst (const theta')
      return (subst theta' $ TypeConstructor qi tys)
    info -> internalError $ "Base.Typing.argType: Expected record type but got "
              ++ show info

fieldPattType :: Field Pattern -> TCM (Ident,Type)
fieldPattType (Field _ l t) = do
  tyEnv <- getValueEnv
  lty   <- instUniv (labelType l tyEnv)
  ty    <- argType t
  unify lty ty
  return (l,lty)

exprType :: ValueEnv -> Expression -> TyState Type
exprType tyEnv (Literal l) = litType tyEnv l
exprType tyEnv (Variable _ v) = instUniv (funType v tyEnv)
exprType tyEnv (Constructor c) = instUnivExist (constrType c tyEnv)
exprType tyEnv (Typed _ e _ _) = exprType tyEnv e
exprType tyEnv (Paren e) = exprType tyEnv e
exprType tyEnv (Tuple _ es)
  | null es = return unitType
  | otherwise = liftM tupleType $ mapM (exprType tyEnv) es
exprType tyEnv (List _ es) = freshTypeVar >>= flip elemType es
  where elemType ty [] = return (listType ty)
        elemType ty (e:es1) =
          exprType tyEnv e >>= unify ty >> elemType ty es1
exprType tyEnv (ListCompr _ e _) = liftM listType $ exprType tyEnv e
-- the following equations for exprType should never be needed when the
-- type class extensions are enabled, because the dictionaries transformation
-- removes the Enum* data constructors from the AST, hence it should be 
-- OK to return only the type [Int] 
exprType _     (EnumFrom (Just _cty) _) = return (listType intType)
exprType _     (EnumFrom Nothing _) = internalError "exprType EnumFrom"
exprType _     (EnumFromThen (Just _cty) _ _) = return (listType intType)
exprType _     (EnumFromThen Nothing _ _) = internalError "exprType EnumFromThen"
exprType _     (EnumFromTo (Just _cty) _ _) = return (listType intType)
exprType _     (EnumFromTo Nothing _ _) = internalError "exprType EnumFromTo"
exprType _     (EnumFromThenTo (Just _cty) _ _ _) = return (listType intType)
exprType _     (EnumFromThenTo Nothing _ _ _) = internalError "exprType EnumFromThenTo"
exprType tyEnv (UnaryMinus _ _ e) = exprType tyEnv e
exprType tyEnv (Apply e1 e2) = do
    (ty1,ty2) <- exprType tyEnv e1 >>= unifyArrow
    exprType tyEnv e2 >>= unify ty1
    return ty2
exprType tyEnv (InfixApply e1 op e2) = do
    (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
    exprType tyEnv e1 >>= unify ty1
    exprType tyEnv e2 >>= unify ty2
    return ty3
exprType tyEnv (LeftSection e op) = do
    (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
    exprType tyEnv e >>= unify ty1
    return (TypeArrow ty2 ty3)
exprType tyEnv (RightSection op e) = do
    (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
    exprType tyEnv e >>= unify ty2
    return (TypeArrow ty1 ty3)
exprType tyEnv (Lambda _ args e) = do
    tys <- mapM (argType tyEnv) args
    ty <- exprType tyEnv e
    return (foldr TypeArrow ty tys)
exprType tyEnv (Let _ e) = exprType tyEnv e
exprType tyEnv (Do _ e) = exprType tyEnv e
exprType tyEnv (IfThenElse _ e1 e2 e3) = do
    exprType tyEnv e1 >>= unify boolType
    ty2 <- exprType tyEnv e2
    ty3 <- exprType tyEnv e3
    unify ty2 ty3
    return ty3
exprType tyEnv (Case _ _ _ alts) = freshTypeVar >>= flip altType alts
  where altType ty [] = return ty
        altType ty (Alt _ _ rhs:alts1) =
          rhsType rhs >>= unify ty >> altType ty alts1
exprType (RecordConstr fs) = do
  recInfo <- getFieldIdent fs >>= getRecordInfo
  case recInfo of
    [AliasType qi n rty@(TypeRecord _)] -> do
      (TypeRecord fts', tys) <- instType' n rty
      fts   <- mapM fieldExprType fs
      theta <- getTypeSubst
      let theta' = foldr (unifyTypedLabels fts') theta fts
      modifyTypeSubst (const theta')
      return (subst theta' $ TypeConstructor qi tys)
    info -> internalError $
      "Base.Typing.exprType: Expected record type but got " ++ show info
exprType (RecordSelection e l) = do
  recInfo <- getRecordInfo l
  case recInfo of
    [AliasType qi n rty@(TypeRecord _)] -> do
      (TypeRecord fts, tys) <- instType' n rty
      ety <- exprType e
      let rtc = TypeConstructor qi tys
      case lookup l fts of
        Just lty -> do
          unify ety rtc
          theta <- getTypeSubst
          return (subst theta lty)
        Nothing -> internalError "Base.Typing.exprType: Field not found."
    info -> internalError $
      "Base.Typing.exprType: Expected record type but got " ++ show info
exprType (RecordUpdate fs e) = do
  recInfo <- getFieldIdent fs >>= getRecordInfo
  case recInfo of
    [AliasType qi n rty@(TypeRecord _)] -> do
      (TypeRecord fts', tys) <- instType' n rty
      -- Type check field updates
      fts <- mapM fieldExprType fs
      modifyTypeSubst (\s -> foldr (unifyTypedLabels fts') s fts)
      -- Type check record expression to be updated
      ety <- exprType e
      let rtc = TypeConstructor qi tys
      unify ety rtc
      -- Return inferred type
      theta <- getTypeSubst
      return (subst theta rtc)
    info -> internalError $
      "Base.Typing.exprType: Expected record type but got " ++ show info

rhsType :: Rhs -> TCM Type
rhsType (SimpleRhs _ e _) = exprType e
rhsType (GuardedRhs es _) = freshTypeVar >>= flip condExprType es
  where condExprType ty [] = return ty
        condExprType ty (CondExpr _ _ e:es1) =
          exprType e >>= unify ty >> condExprType ty es1

fieldExprType :: Field Expression -> TCM (Ident,Type)
fieldExprType (Field _ l e) = do
  tyEnv <- getValueEnv
  lty   <- instUniv (labelType l tyEnv)
  ty    <- exprType e
  unify lty ty
  return (l,lty)

-- In order to avoid name conflicts with non-generalized type variables
-- in a type we instantiate quantified type variables using non-negative
-- offsets here.

freshTypeVar :: TCM Type
freshTypeVar = TypeVariable `liftM` getNextId

instType :: Int -> Type -> TCM Type
instType n ty = do
  tys <- replicateM n freshTypeVar
  return (expandAliasType tys ty)

instType' :: Int -> Type -> TCM (Type,[Type])
instType' n ty = do
  tys <- replicateM n freshTypeVar
  return (expandAliasType tys ty, tys)

instUniv :: TypeScheme -> TyState Type
instUniv (ForAll _cx n ty) = instType n ty

instUnivExist :: ExistTypeScheme -> TyState Type
instUnivExist (ForAllExist _cx n n' ty) = instType (n + n') ty

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
unifyTypes (TypeRecord fs1) (TypeRecord fs2) theta
  | length fs1 == length fs2 = foldr (unifyTypedLabels fs1) theta fs2
unifyTypes ty1 ty2 _ = internalError $
  "Base.Typing.unify: (" ++ show ty1 ++ ") (" ++ show ty2 ++ ")"

-- jrt 2014-10-20: Deactivated because the parser can not parse
-- record extensions, thus, these cases should never occur. If they do,
-- there must be an error somewhere ...
-- unifyTypes tr1@(TypeRecord fs1 Nothing) (TypeRecord fs2 (Just a2)) theta =
--   unifyTypes (TypeVariable a2)
--              tr1
--              (foldr (unifyTypedLabels fs1) theta fs2)
-- unifyTypes tr1@(TypeRecord _ (Just _)) tr2@(TypeRecord _ Nothing) theta =
--   unifyTypes tr2 tr1 theta
-- unifyTypes (TypeRecord fs1 (Just a1)) (TypeRecord fs2 (Just a2)) theta =
--   unifyTypes (TypeVariable a1)
--              (TypeVariable a2)
--              (foldr (unifyTypedLabels fs1) theta fs2)

unifyTypedLabels :: [(Ident,Type)] -> (Ident,Type) -> TypeSubst -> TypeSubst
unifyTypedLabels fs1 (l,ty) theta =
  maybe theta (\ty1 -> unifyTypes ty1 ty theta) (lookup l fs1)

getFieldIdent :: [Field a] -> TCM Ident
getFieldIdent [] = internalError "Base.Typing.getFieldIdent: empty field"
getFieldIdent (Field _ i _ : _) = return i

-- Lookup record type for given field identifier
getRecordInfo :: Ident -> TCM [TypeInfo]
getRecordInfo i = do
  tyEnv <- getValueEnv
  tcEnv <- getTyConsEnv
  case lookupValue i tyEnv of
       [Label _ r _] -> return (qualLookupTC r tcEnv)
       _             -> internalError $
        "Base.Typing.getRecordInfo: No record found for identifier " ++ show i

-- The functions 'constrType', 'varType', and 'funType' are used for computing
-- the type of constructors, pattern variables, and variables.

-- TODO: These functions should be shared with the type checker.

constrType :: QualIdent -> ValueEnv -> ExistTypeScheme
constrType c tyEnv = case qualLookupValue c tyEnv of
  [DataConstructor  _ _ sigma] -> sigma
  [NewtypeConstructor _ sigma] -> sigma
  _ -> internalError $ "Base.Typing.constrType: " ++ show c

varType :: Ident -> ValueEnv -> TypeScheme
varType v tyEnv = case lookupValue v tyEnv of
  [Value _ _ sigma _] -> sigma
  _ -> internalError $ "Base.Typing.varType: " ++ show v

funType :: QualIdent -> ValueEnv -> TypeScheme
funType f tyEnv = case qualLookupValue f tyEnv of
  [Value _ _ sigma _] -> sigma
  _ -> internalError $ "Base.Typing.funType: " ++ show f

labelType :: Ident -> ValueEnv -> TypeScheme
labelType l tyEnv = case lookupValue l tyEnv of
  [Label _ _ sigma] -> sigma
  _ -> internalError $ "Base.Typing.labelType: " ++ show l
