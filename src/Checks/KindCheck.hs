{- |
    Module      :  $Header$
    Description :  Checks type kinds
    Copyright   :  (c)        2016 Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After the type syntax has been checked und nullary type constructors and
   type variables have been disambiguated, the compiler infers kinds for all
   type constructors and type classes defined in the current module and
   performs kind checking on all type definitions and type signatures.
-}
{-# LANGUAGE CPP #-}
module Checks.KindCheck (kindCheck) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>))
#endif
import           Control.Monad            (when, foldM)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import           Data.List                (partition, nub)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.CurryKinds
import Base.CurryTypes
import Base.Expr
import Base.Kinds
import Base.KindSubst
import Base.Messages (Message, posMessage, internalError)
import Base.SCC
import Base.TopEnv
import Base.Types

import Env.TypeConstructor

-- In order to infer kinds for type constructors and type classes, the
-- compiler sorts the module's type and class declarations into minimal
-- recursive binding groups and then applies kind inference to each
-- declaration group. Besides inferring kinds for the type constructors
-- and type classes of a group, the compiler also checks that there are
-- no mutually recursive type synonym definitions and that the super class
-- hierarchy is acyclic.

kindCheck :: TCEnv -> Module -> (TCEnv, [Message])
kindCheck tcEnv (Module _ m _ _ ds) = runKCM check initState
  where
    check = do
      checkTypeSynonyms tds &&> checkSuperClasses cds
      errs <- S.gets errors
      if null errs
         then checkDecls
         else return tcEnv
    checkDecls = do
      tcEnv' <- kcDecls tcEnv tcds
      mapM_ (kcDecl tcEnv') ods
      return tcEnv'
    tds = filter isTypeDecl tcds
    cds = filter isClassDecl tcds
    (tcds, ods) = partition isTypeOrClassDecl ds
    initState  = KCState m idSubst 0 []

-- Kind Check Monad
type KCM = S.State KCState

-- |Internal state of the Kind Check
data KCState = KCState
  { moduleIdent :: ModuleIdent -- read only
  , kindSubst   :: KindSubst
  , nextId      :: Int         -- automatic counter
  , errors      :: [Message]
  }

(&&>) :: KCM () -> KCM () -> KCM ()
pre &&> suf = do
  errs <- pre >> S.gets errors
  if null errs then suf else return ()

runKCM :: KCM a -> KCState -> (a, [Message])
runKCM kcm s = let (a, s') = S.runState kcm s in (a, reverse $ errors s')

getModuleIdent :: KCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getKindSubst :: KCM KindSubst
getKindSubst = S.gets kindSubst

modifyKindSubst :: (KindSubst -> KindSubst) -> KCM ()
modifyKindSubst f = S.modify $ \s -> s { kindSubst = f $ kindSubst s }

getNextId :: KCM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

report :: Message -> KCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: KCM ()
ok = return ()

-- Minimal recursive declaration groups are computed using the sets of bound
-- and free type constructor and type class identifiers of the declarations.

bt :: Decl -> [Ident]
bt (DataDecl       _ tc _ _) = [tc]
bt (NewtypeDecl    _ tc _ _) = [tc]
bt (TypeDecl       _ tc _ _) = [tc]
bt (ClassDecl   _ _ cls _ _) = [cls]
bt _                         = []

ft :: ModuleIdent -> Decl -> [Ident]
ft m d = fts m d []

class HasType a where
  fts :: ModuleIdent -> a -> [Ident] -> [Ident]

instance HasType a => HasType [a] where
  fts m = flip $ foldr $ fts m

instance HasType a => HasType (Maybe a) where
  fts m = maybe id $ fts m

instance HasType Decl where
  fts _ (InfixDecl              _ _ _ _) = id
  fts m (DataDecl              _ _ _ cs) = fts m cs
  fts m (NewtypeDecl           _ _ _ nc) = fts m nc
  fts m (TypeDecl              _ _ _ ty) = fts m ty
  fts m (TypeSig                 _ _ ty) = fts m ty
  fts m (FunctionDecl           _ _ eqs) = fts m eqs
  fts m (ForeignDecl         _ _ _ _ ty) = fts m ty
  fts _ (ExternalDecl               _ _) = id
  fts m (PatternDecl            _ _ rhs) = fts m rhs
  fts _ (FreeDecl                   _ _) = id
  fts m (ClassDecl         _ scx _ _ ds) = fts m scx . fts m ds
  fts m (InstanceDecl _ scx cls inst ds) =
    -- TODO: fts m inst
    fts m scx . fts m cls . fts m ds

instance HasType ConstrDecl where
  fts m (ConstrDecl     _ _ _ tys) = fts m tys
  fts m (ConOpDecl  _ _ ty1 _ ty2) = fts m ty1 . fts m ty2
  fts m (RecordDecl      _ _ _ fs) = fts m fs

instance HasType FieldDecl where
  fts m (FieldDecl _ _ ty) = fts m ty

instance HasType NewConstrDecl where
  fts m (NewConstrDecl      _ _ _ ty) = fts m ty
  fts m (NewRecordDecl _ _ _ (_, ty)) = fts m ty

instance HasType SimpleContext where
  fts m (SimpleContext       sc) = fts m sc
  fts m (ParenSimpleContext scs) = fts m scs

instance HasType SimpleConstraint where
  fts m (SimpleConstraint (qcls, _)) = fts m qcls

instance HasType TypeExpr where
  fts m (ConstructorType      tc) = fts m tc
  fts m (ApplyType       ty1 ty2) = fts m ty1 . fts m ty2
  fts _ (VariableType          _) = id
  fts m (TupleType           tys) = (tupleId (length tys) :) . fts m tys
  fts m (ListType             ty) = (listId :) . fts m ty
  fts m (ArrowType       ty1 ty2) = fts m ty1 . fts m ty2
  fts m (ParenType            ty) = fts m ty

instance HasType Equation where
  fts m (Equation _ _ rhs) = fts m rhs

instance HasType Rhs where
  fts m (SimpleRhs  _ e ds) = fts m e . fts m ds
  fts m (GuardedRhs  es ds) = fts m es . fts m ds

instance HasType CondExpr where
  fts m (CondExpr _ g e) = fts m g . fts m e

instance HasType Expression where
  fts _ (Literal               _) = id
  fts _ (Variable              _) = id
  fts _ (Constructor           _) = id
  fts m (Paren                 e) = fts m e
  fts m (Typed              e ty) = fts m e . fts m ty
  fts m (Record             _ fs) = fts m fs
  fts m (RecordUpdate       e fs) = fts m e . fts m fs
  fts m (Tuple              _ es) = fts m es
  fts m (List               _ es) = fts m es
  fts m (ListCompr      _ e stms) = fts m e . fts m stms
  fts m (EnumFrom              e) = fts m e
  fts m (EnumFromThen      e1 e2) = fts m e1 . fts m e2
  fts m (EnumFromTo        e1 e2) = fts m e1 . fts m e2
  fts m (EnumFromThenTo e1 e2 e3) = fts m e1 . fts m e2 . fts m e3
  fts m (UnaryMinus          _ e) = fts m e
  fts m (Apply             e1 e2) = fts m e1 . fts m e2
  fts m (InfixApply      e1 _ e2) = fts m e1 . fts m e2
  fts m (LeftSection         e _) = fts m e
  fts m (RightSection        _ e) = fts m e
  fts m (Lambda            _ _ e) = fts m e
  fts m (Let                ds e) = fts m ds . fts m e
  fts m (Do               stms e) = fts m stms . fts m e
  fts m (IfThenElse   _ e1 e2 e3) = fts m e1 . fts m e2 . fts m e3
  fts m (Case           _ _ e as) = fts m e . fts m as

instance HasType Statement where
  fts m (StmtExpr   _ e) = fts m e
  fts m (StmtDecl    ds) = fts m ds
  fts m (StmtBind _ _ e) = fts m e

instance HasType Alt where
  fts m (Alt _ _ rhs) = fts m rhs

instance HasType a => HasType (Field a) where
  fts m (Field _ _ x) = fts m x

instance HasType QualIdent where
  fts m qident = maybe id (:) (localIdent m qident)

-- Curry does not allow (mutually) recursive type synonyms, which is checked
-- in the function 'checkTypeSynonyms' below.

checkTypeSynonyms :: [Decl] -> KCM ()
checkTypeSynonyms ds = do
  m <- getModuleIdent
  mapM_ checkTypeDecls $ scc bt (ft m) ds

checkTypeDecls :: [Decl] -> KCM ()
checkTypeDecls [] =
  internalError "KindCheck.checkTypeDecls: empty list"
checkTypeDecls [DataDecl _ _ _ _] = ok
checkTypeDecls [NewtypeDecl _ _ _ _] = ok
checkTypeDecls [TypeDecl _ tc _ ty] = do
  m <- getModuleIdent
  when (tc `elem` fts m ty []) $ report $ errRecursiveTypes [tc]
checkTypeDecls (TypeDecl _ tc _ _ : ds) =
  report $ errRecursiveTypes $ tc : [tc' | TypeDecl _ tc' _ _ <- ds]
checkTypeDecls _ =
  internalError "KindCheck.checkTypeDecls: no type declaration"

-- The function 'checkSuperClasses' checks that the super class hierarchy
-- is acyclic.

fc :: ModuleIdent -> Maybe SimpleContext -> [Ident]
fc m = maybe [] fc'
  where
    fc' (SimpleContext       sc) = fc'' sc
    fc' (ParenSimpleContext scs) = concatMap fc'' scs
    fc'' (SimpleConstraint (qcls, _)) = maybe id (:) (localIdent m qcls) []

checkSuperClasses :: [Decl] -> KCM ()
checkSuperClasses ds = do
  m <- getModuleIdent
  mapM_ checkClassDecl $ scc bt (\(ClassDecl _ scx _ _ _) -> fc m scx) ds

checkClassDecl :: [Decl] -> KCM ()
checkClassDecl [] =
  internalError "KindCheck.checkClassDecl: empty list"
checkClassDecl [ClassDecl _ cx cls _ _] = do
  m <- getModuleIdent
  when (cls `elem` fc m cx) $ report $ errRecursiveClasses [cls]
checkClassDecl (ClassDecl _ _ cls _ _ : ds) =
  report $ errRecursiveClasses $ cls : [cls' | ClassDecl _ _ cls' _ _ <- ds]
checkClassDecl _ =
  internalError "KindCheck.checkClassDecl: no class declaration"

-- For each declaration group, the kind checker first enters new
-- assumptions into the type constructor environment. For a type
-- constructor with arity n, we enter kind k_1 -> ... -> k_n -> k,
-- where k_i are fresh kind variables and k is * for data and newtype
-- type constructors and a fresh kind variable for type synonym type
-- constructors. For a type class we enter kind k, where k is a fresh
-- kind variable. Next, the kind checker checks the declarations of the
-- group within the extended environment, and finally the kind checker
-- instantiates all remaining free kind variables to *.

bindKind :: TCEnv -> Decl -> KCM TCEnv
bindKind tcEnv (DataDecl _ tc tvs cs) =
  bindTypeConstructor DataType tc tvs (Just KindStar) (map mkData cs) tcEnv
  where
    mkData (ConstrDecl _ evs     c  tys) = mkData' evs c  tys
    mkData (ConOpDecl  _ evs ty1 op ty2) = mkData' evs op [ty1, ty2]
    mkData (RecordDecl _ evs     c   fs) =
      let (labels, tys) = unzip [(l, ty) | FieldDecl _ ls ty <- fs, l <- ls]
      in  mkRec evs c labels tys
    mkData' evs c tys =
      DataConstr c (length evs) $ map (toType (evs ++ tvs)) tys
    mkRec evs c ls tys =
      RecordConstr c (length evs) ls $ map (toType (evs ++ tvs)) tys
bindKind tcEnv (NewtypeDecl _ tc tvs nc) =
  bindTypeConstructor RenamingType tc tvs (Just KindStar) (mkData nc) tcEnv
  where
    mkData (NewConstrDecl _ evs c      ty) =
      DataConstr c (length evs) [toType (tvs ++ evs) ty]
    mkData (NewRecordDecl _ evs c (l, ty)) =
      RecordConstr c (length evs) [l] [toType (tvs ++ evs) ty]
bindKind tcEnv (TypeDecl _ tc tvs ty) =
  bindTypeConstructor aliasType tc tvs Nothing (toType tvs ty) tcEnv
  where
    aliasType tc' k = AliasType tc' k $ length tvs
bindKind tcEnv (ClassDecl _ scx cls _ ds) =
  bindTypeClass cls (maybe [] superclasses scx) (maybe [] (concatMap methods) ds) tcEnv
  where
    superclasses cx = [qcls | SimpleConstraint (qcls, _) <- constraints cx]
    constraints (SimpleContext sc) = [sc]
    constraints (ParenSimpleContext scs) = scs
bindKind tcEnv _                     = return tcEnv

bindTypeConstructor :: (QualIdent -> Kind -> a -> TypeInfo) -> Ident
                    -> [Ident] -> Maybe Kind -> a -> TCEnv -> KCM TCEnv
bindTypeConstructor f tc tvs k x tcEnv = do
  m <- getModuleIdent
  k' <- maybe freshKindVar return k
  ks <- mapM (const freshKindVar) tvs
  let qtc = qualifyWith m tc
      ti = f qtc (foldr KindArrow k' ks) x
  return $ bindTypeInfo m tc ti tcEnv

bindTypeClass :: Ident -> [QualIdent] -> [Ident] -> TCEnv -> KCM TCEnv
bindTypeClass cls sclss ms tcEnv = do
  m <- getModuleIdent
  k <- freshKindVar
  let qcls = qualifyWith m cls
      ti = TypeClass qcls k sclss ms
  return $ bindTypeInfo m cls ti tcEnv

bindFreshKind :: TCEnv -> Ident -> KCM TCEnv
bindFreshKind tcEnv tv = do
  k <- freshKindVar
  return $ bindTypeVar tv k tcEnv

bindTypeVars :: Ident -> [Ident] -> TCEnv -> KCM (Kind, TCEnv)
bindTypeVars tc tvs tcEnv = do
  m <- getModuleIdent
  return $ foldl (\(KindArrow k1 k2, tcEnv') tv ->
                   (k2, bindTypeVar tv k1 tcEnv'))
                 (tcKind (qualifyWith m tc) tcEnv, tcEnv)
                 tvs

bindTypeVar :: Ident -> Kind -> TCEnv -> TCEnv
bindTypeVar ident k = bindTopEnv ident (TypeVar k)

instantiateWithDefaultKind :: TypeInfo -> TypeInfo
instantiateWithDefaultKind (DataType tc k cs) =
  DataType tc (defaultKind k) cs
instantiateWithDefaultKind (RenamingType tc k nc) =
  RenamingType tc (defaultKind k) nc
instantiateWithDefaultKind (AliasType tc k n ty) =
  AliasType tc (defaultKind k) n ty
instantiateWithDefaultKind (TypeClass cls k sclss ms) =
  TypeClass cls (defaultKind k) sclss ms
instantiateWithDefaultKind (TypeVar _) =
  internalError "Checks.KindCheck.instantiateWithDefaultKind: type variable"

kcDecls :: TCEnv -> [Decl] -> KCM TCEnv
kcDecls tcEnv ds = do
  m <- getModuleIdent
  foldM kcDeclGroup tcEnv $ scc bt (ft m) ds

kcDeclGroup :: TCEnv -> [Decl] -> KCM TCEnv
kcDeclGroup tcEnv ds = do
  tcEnv' <- foldM bindKind tcEnv ds
  mapM_ (kcDecl tcEnv') ds
  theta <- getKindSubst
  return $ fmap (instantiateWithDefaultKind . subst theta) tcEnv'

-- After adding new assumptions to the environment, kind inference is
-- applied to all declarations. The type environment may be extended
-- temporarily with bindings for type variables occurring in the left
-- hand side of type declarations and free type variables of type
-- signatures. While the kinds of the former are determined already by
-- the kinds of their type constructors and type classes, respectively,
-- fresh kind variables are added for the latter.

kcDecl :: TCEnv -> Decl -> KCM ()
kcDecl _     (InfixDecl _ _ _ _) = ok
kcDecl tcEnv (DataDecl _ tc tvs cs) = do
  (_, tcEnv') <- bindTypeVars tc tvs tcEnv
  mapM_ (kcConstrDecl tcEnv') cs
kcDecl tcEnv (NewtypeDecl _ tc tvs nc) = do
  (_, tcEnv') <- bindTypeVars tc tvs tcEnv
  kcNewConstrDecl tcEnv' nc
kcDecl tcEnv t@(TypeDecl p tc tvs ty) = do
  (k, tcEnv') <- bindTypeVars tc tvs tcEnv
  kcType tcEnv' p "type declaration" (ppDecl t) k ty
kcDecl tcEnv (TypeSig p _ ty) = kcTypeSig tcEnv p ty
kcDecl tcEnv (FunctionDecl _ _ eqs) = mapM_ (kcEquation tcEnv) eqs
kcDecl tcEnv (ForeignDecl p _ _ _ ty) = kcTypeSig tcEnv p ty
kcDecl tcEnv (PatternDecl _ _ rhs) = kcRhs tcEnv rhs
kcDecl _     (FreeDecl _ _) = ok
kcDecl tcEnv (ClassDecl p scx cls tv ds) = do
  m <- getModuleIdent
  let tcEnv' = bindTypeVar tv (classKind (qualifyWith m cls) tcEnv) tcEnv
  maybe ok (kcSimpleContext tcEnv' p) scx
  maybe ok (mapM_ (kcDecl tcEnv')) ds
kcDecl _ _ =
  internalError "Checks.KindCheck.kcDecl: not yet implemented"

kcConstrDecl :: TCEnv -> ConstrDecl -> KCM ()
kcConstrDecl tcEnv d@(ConstrDecl p evs _ tys) = do
  tcEnv' <- foldM bindFreshKind tcEnv evs
  mapM_ (kcValueType tcEnv' p what doc) tys
    where
      what = "data constructor declaration"
      doc = ppConstr d
kcConstrDecl tcEnv d@(ConOpDecl p evs ty1 _ ty2) = do
  tcEnv' <- foldM bindFreshKind tcEnv evs
  kcValueType tcEnv' p what doc ty1
  kcValueType tcEnv' p what doc ty2
    where
      what = "data constructor declaration"
      doc = ppConstr d
kcConstrDecl tcEnv (RecordDecl _ evs _ fs) = do
  tcEnv' <- foldM bindFreshKind tcEnv evs
  mapM_ (kcFieldDecl tcEnv') fs

kcFieldDecl :: TCEnv -> FieldDecl -> KCM ()
kcFieldDecl tcEnv d@(FieldDecl p _ ty) =
  kcValueType tcEnv p "field declaration" (ppFieldDecl d) ty

kcNewConstrDecl :: TCEnv -> NewConstrDecl -> KCM ()
kcNewConstrDecl tcEnv d@(NewConstrDecl p evs _ ty) = do
  tcEnv' <- foldM bindFreshKind tcEnv evs
  kcValueType tcEnv' p "newtype constructor declaration" (ppNewConstr d) ty
kcNewConstrDecl tcEnv (NewRecordDecl p evs _ (l, ty)) = do
  tcEnv' <- foldM bindFreshKind tcEnv evs
  kcFieldDecl tcEnv' (FieldDecl p [l] ty)

kcEquation :: TCEnv -> Equation -> KCM ()
kcEquation tcEnv (Equation _ _ rhs) = kcRhs tcEnv rhs

kcRhs :: TCEnv -> Rhs -> KCM ()
kcRhs tcEnv (SimpleRhs p e ds) = do
  kcExpr tcEnv p e
  mapM_ (kcDecl tcEnv) ds
kcRhs tcEnv (GuardedRhs es ds) = do
  mapM_ (kcCondExpr tcEnv) es
  mapM_ (kcDecl tcEnv) ds

kcCondExpr :: TCEnv -> CondExpr -> KCM ()
kcCondExpr tcEnv (CondExpr p g e) = kcExpr tcEnv p g >> kcExpr tcEnv p e

kcExpr :: TCEnv -> Position -> Expression -> KCM ()
kcExpr _     _ (Literal _) = ok
kcExpr _     _ (Variable _) = ok
kcExpr _     _ (Constructor _) = ok
kcExpr tcEnv p (Paren e) = kcExpr tcEnv p e
kcExpr tcEnv p (Typed e ty) = do
  kcExpr tcEnv p e
  kcTypeSig tcEnv p ty
kcExpr tcEnv p (Record _ fs) = mapM_ (kcField tcEnv p) fs
kcExpr tcEnv p (RecordUpdate e fs) = do
  kcExpr tcEnv p e
  mapM_ (kcField tcEnv p) fs
kcExpr tcEnv p (Tuple _ es) = mapM_ (kcExpr tcEnv p) es
kcExpr tcEnv p (List _ es) = mapM_ (kcExpr tcEnv p) es
kcExpr tcEnv p (ListCompr _ e stms) = do
  kcExpr tcEnv p e
  mapM_ (kcStmt tcEnv p) stms
kcExpr tcEnv p (EnumFrom e) = kcExpr tcEnv p e
kcExpr tcEnv p (EnumFromThen e1 e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (EnumFromTo e1 e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (EnumFromThenTo e1 e2 e3) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
  kcExpr tcEnv p e3
kcExpr tcEnv p (UnaryMinus _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Apply e1 e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (InfixApply e1 _ e2) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
kcExpr tcEnv p (LeftSection e _) = kcExpr tcEnv p e
kcExpr tcEnv p (RightSection _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Lambda _ _ e) = kcExpr tcEnv p e
kcExpr tcEnv p (Let ds e) = do
  mapM_ (kcDecl tcEnv) ds
  kcExpr tcEnv p e
kcExpr tcEnv p (Do stms e) = do
  mapM_ (kcStmt tcEnv p) stms
  kcExpr tcEnv p e
kcExpr tcEnv p (IfThenElse _ e1 e2 e3) = do
  kcExpr tcEnv p e1
  kcExpr tcEnv p e2
  kcExpr tcEnv p e3
kcExpr tcEnv p (Case _ _ e alts) = do
  kcExpr tcEnv p e
  mapM_ (kcAlt tcEnv) alts

kcStmt :: TCEnv -> Position -> Statement -> KCM ()
kcStmt tcEnv p (StmtExpr _ e) = kcExpr tcEnv p e
kcStmt tcEnv _ (StmtDecl ds) = mapM_ (kcDecl tcEnv) ds
kcStmt tcEnv p (StmtBind _ _ e) = kcExpr tcEnv p e

kcAlt :: TCEnv -> Alt -> KCM ()
kcAlt tcEnv (Alt _ _ rhs) = kcRhs tcEnv rhs

kcField :: TCEnv -> Position -> Field Expression -> KCM ()
kcField tcEnv p (Field _ _ e) = kcExpr tcEnv p e

kcSimpleContext :: TCEnv -> Position -> SimpleContext -> KCM ()
kcSimpleContext tcEnv p (SimpleContext sc) = kcSimpleConstraint tcEnv p sc
kcSimpleContext tcEnv p (ParenSimpleContext scs) =
  mapM_ (kcSimpleConstraint tcEnv p) scs

kcSimpleConstraint :: TCEnv -> Position -> SimpleConstraint -> KCM ()
kcSimpleConstraint tcEnv p sc@(SimpleConstraint (qcls, tv)) =
  kcType tcEnv p "class constraint" doc (classKind qcls tcEnv) (VariableType tv)
  where
    doc = ppSimpleConstraint sc

kcTypeSig :: TCEnv -> Position -> TypeExpr -> KCM ()
kcTypeSig tcEnv p ty = do
  tcEnv' <- foldM bindFreshKind tcEnv free
  kcValueType tcEnv' p "type signature" doc ty
  where
    free = filter (null . flip lookupTypeInfo tcEnv) $ nub $ fv ty
    doc = ppTypeExpr 0 ty

kcValueType :: TCEnv -> Position -> String -> Doc -> TypeExpr -> KCM ()
kcValueType tcEnv p what doc = kcType tcEnv p what doc KindStar

kcType :: TCEnv -> Position -> String -> Doc -> Kind -> TypeExpr -> KCM ()
kcType tcEnv p what doc k ty = do
  k' <- kcTypeExpr tcEnv p "type expression" doc' 0 ty
  unify p what (doc $-$ text "Type:" <+> doc') k k'
  where
    doc' = ppTypeExpr 0 ty

kcTypeExpr :: TCEnv -> Position -> String -> Doc -> Int -> TypeExpr -> KCM Kind
kcTypeExpr tcEnv p _ _ n (ConstructorType tc) =
  case qualLookupTypeInfo tc tcEnv of
    [AliasType _ _ n' _] -> case n >= n' of
      True -> return $ tcKind tc tcEnv
      False -> do
        report $ errPartialAlias p tc n' n
        freshKindVar
    _ -> return $ tcKind tc tcEnv
kcTypeExpr tcEnv p what doc n (ApplyType ty1 ty2) = do
  (alpha, beta) <- kcTypeExpr tcEnv p what doc (n + 1) ty1 >>=
    kcArrow p what (doc $-$ text "Type:" <+> ppTypeExpr 0 ty1)
  kcTypeExpr tcEnv p what doc 0 ty2 >>=
    unify p what (doc $-$ text "Type:" <+> ppTypeExpr 0 ty2) alpha
  return beta
kcTypeExpr tcEnv _ _ _ _ (VariableType tv) = return (varKind tv tcEnv)
kcTypeExpr tcEnv p what doc _ (TupleType tys) = do
  mapM_ (kcValueType tcEnv p what doc) tys
  return KindStar
kcTypeExpr tcEnv p what doc _ (ListType ty) = do
  kcValueType tcEnv p what doc ty
  return KindStar
kcTypeExpr tcEnv p what doc _ (ArrowType ty1 ty2) = do
  kcValueType tcEnv p what doc ty1
  kcValueType tcEnv p what doc ty2
  return KindStar
kcTypeExpr tcEnv p what doc n (ParenType ty) = kcTypeExpr tcEnv p what doc n ty

kcArrow :: Position -> String -> Doc -> Kind -> KCM (Kind, Kind)
kcArrow p what doc k = do
  theta <- getKindSubst
  case subst theta k of
    KindStar -> do
      report $ errNonArrowKind p what doc KindStar
      (,) <$> freshKindVar <*> freshKindVar
    KindVariable kv -> do
      alpha <- freshKindVar
      beta <- freshKindVar
      modifyKindSubst $ bindVar kv $ KindArrow alpha beta
      return (alpha, beta)
    KindArrow k1 k2 -> return (k1, k2)

-- ---------------------------------------------------------------------------
-- Unification
-- ---------------------------------------------------------------------------

-- The unification uses Robinson's algorithm.
unify :: Position -> String -> Doc -> Kind -> Kind -> KCM ()
unify p what doc k1 k2 = do
  theta <- getKindSubst
  let k1' = subst theta k1
  let k2' = subst theta k2
  case unifyKinds k1' k2' of
    Nothing -> report $ errKindMismatch p what doc k1' k2'
    Just sigma -> modifyKindSubst (compose sigma)

unifyKinds :: Kind -> Kind -> Maybe KindSubst
unifyKinds KindStar KindStar = Just idSubst
unifyKinds (KindVariable kv1) (KindVariable kv2)
  | kv1 == kv2 = Just idSubst
  | otherwise  = Just (singleSubst kv1 (KindVariable kv2))
unifyKinds (KindVariable kv) k
  | kv `elem` kindVars k = Nothing
  | otherwise            = Just (singleSubst kv k)
unifyKinds k (KindVariable kv)
  | kv `elem` kindVars k = Nothing
  | otherwise            = Just (singleSubst kv k)
unifyKinds (KindArrow k11 k12) (KindArrow k21 k22) = do
  theta <- unifyKinds k11 k21
  theta' <- unifyKinds (subst theta k12) (subst theta k22)
  Just (compose theta' theta)
unifyKinds _ _ = Nothing

-- ---------------------------------------------------------------------------
-- Fresh variables
-- ---------------------------------------------------------------------------

fresh :: (Int -> a) -> KCM a
fresh f = f <$> getNextId

freshKindVar :: KCM Kind
freshKindVar = fresh KindVariable

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errRecursiveTypes :: [Ident] -> Message
errRecursiveTypes []       = internalError
  "KindCheck.errRecursiveTypes: empty list"
errRecursiveTypes [tc]     = posMessage tc $ hsep $ map text
  ["Recursive synonym type", idName tc]
errRecursiveTypes (tc:tcs) = posMessage tc $
  text "Mutually recursive synonym types" <+> text (idName tc) <>
    types empty tcs
  where
    types _   []         = empty
    types del [tc']      = del <> space <> text "and" <+> typePos tc'
    types _   (tc':tcs') = comma <+> typePos tc' <> types comma tcs'
    typePos tc' =
      text (idName tc') <+> parens (text $ showLine $ idPosition tc')

errRecursiveClasses :: [Ident] -> Message
errRecursiveClasses []         = internalError
  "KindCheck.errRecursiveClasses: empty list"
errRecursiveClasses [cls]      = posMessage cls $ hsep $ map text
  ["Recursive type class", idName cls]
errRecursiveClasses (cls:clss) = posMessage cls $
  text "Mutually recursive type classes" <+> text (idName cls) <>
    classes empty clss
  where
    classes _   []           = empty
    classes del [cls']       = del <> space <> text "and" <+> classPos cls'
    classes _   (cls':clss') = comma <+> classPos cls' <> classes comma clss'
    classPos cls' =
      text (idName cls') <+> parens (text $ showLine $ idPosition cls')

errNonArrowKind :: Position -> String -> Doc -> Kind -> Message
errNonArrowKind p what doc k = posMessage p $ vcat
  [ text "Kind error in" <+> text what, doc
  , text "Kind:" <+> ppKind k
  , text "Cannot be applied"
  ]

errPartialAlias :: Position -> QualIdent -> Int -> Int -> Message
errPartialAlias p tc arity argc = posMessage p $ hsep
  [ text "Type synonym", ppQIdent tc
  , text "requires at least"
  , int arity, text (plural arity "argument") <> comma
  , text "but is applied to only", int argc
  ]
  where
    plural n x = if n == 1 then x else x ++ "s"

errKindMismatch :: Position -> String -> Doc -> Kind -> Kind -> Message
errKindMismatch p what doc k1 k2 = posMessage p $ vcat
  [ text "Kind error in"  <+> text what, doc
  , text "Inferred kind:" <+> ppKind k2
  , text "Expected kind:" <+> ppKind k1
  ]
