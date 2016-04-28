{- |
    Module      :  $Header$
    Description :  Checks interface declarations
    Copyright   :  (c) 2000 - 2007 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Similar to Curry source files, some post-processing has to be applied
   to parsed interface files. In particular, the compiler must
   disambiguate nullary type constructors and type variables. In
   addition, the compiler also checks that all type constructor
   applications are saturated. Since interface files are closed -- i.e.,
   they include declarations of all entities which are defined in other
   modules -- the compiler can perform this check without reference to
   the global environments.
-}

module Checks.InterfaceSyntaxCheck (intfSyntaxCheck) where

import           Control.Monad            (liftM, liftM2, unless, when)
import qualified Control.Monad.State as S
import           Data.List                (nub, partition)
import           Data.Maybe               (isNothing)

import Base.Expr
import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Utils    (findMultiples, findDouble)

import Env.TypeConstructor
import Env.Type

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

data ISCState = ISCState
  { typeEnv :: TypeEnv
  , errors  :: [Message]
  }

type ISC = S.State ISCState

getTypeEnv :: ISC TypeEnv
getTypeEnv = S.gets typeEnv

-- |Report a syntax error
report :: Message -> ISC ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

intfSyntaxCheck :: Interface -> (Interface, [Message])
intfSyntaxCheck (Interface n is ds) = (Interface n is ds', reverse $ errors s')
  where (ds', s') = S.runState (mapM checkIDecl ds) (ISCState env [])
        env = foldr bindType (fmap toTypeKind initTCEnv) ds

-- The compiler requires information about the arity of each defined type
-- constructor as well as information whether the type constructor
-- denotes an algebraic data type, a renaming type, or a type synonym.
-- The latter must not occur in type expressions in interfaces.

bindType :: IDecl -> TypeEnv -> TypeEnv
bindType (IInfixDecl           _ _ _ _) = id
bindType (HidingDataDecl      _ tc _ _) = qualBindTopEnv tc (Data tc [])
bindType (IDataDecl      _ tc _ _ cs _) =
  qualBindTopEnv tc (Data tc (map constrId cs))
bindType (INewtypeDecl   _ tc _ _ nc _) =
  qualBindTopEnv tc (Data tc [nconstrId nc])
bindType (ITypeDecl         _ tc _ _ _) = qualBindTopEnv tc (Alias tc)
bindType (IFunctionDecl        _ _ _ _) = id
bindType (HidingClassDecl  _ _ cls _ _) = qualBindTopEnv cls (Class cls [])
bindType (IClassDecl _ _ cls _ _ ms hs) =
  qualBindTopEnv cls (Class cls (filter (`notElem` hs) (map imethod ms)))
bindType (IInstanceDecl      _ _ _ _ _) = id

-- The checks applied to the interface are similar to those performed
-- during syntax checking of type expressions.

checkIDecl :: IDecl -> ISC IDecl
checkIDecl (IInfixDecl  p fix pr op) = return (IInfixDecl p fix pr op)
checkIDecl (HidingDataDecl p tc k tvs) = do
  checkTypeLhs tvs
  return (HidingDataDecl p tc k tvs)
checkIDecl (IDataDecl p tc k tvs cs hs) = do
  checkTypeLhs tvs
  checkHiddenType tc (cons ++ labels) hs
  cs' <- mapM (checkConstrDecl tvs) cs
  return $ IDataDecl p tc k tvs cs' hs
  where cons   = map constrId cs
        labels = nub $ concatMap recordLabels cs
checkIDecl (INewtypeDecl p tc k tvs nc hs) = do
  checkTypeLhs tvs
  checkHiddenType tc (con : labels) hs
  nc' <- checkNewConstrDecl tvs nc
  return $ INewtypeDecl p tc k tvs nc' hs
  where con    = nconstrId nc
        labels = nrecordLabels nc
checkIDecl (ITypeDecl p tc k tvs ty) = do
  checkTypeLhs tvs
  liftM (ITypeDecl p tc k tvs) (checkClosedType tvs ty)
checkIDecl (IFunctionDecl p f n qty) =
  liftM (IFunctionDecl p f n) (checkQualType qty)
checkIDecl (HidingClassDecl p cx qcls k clsvar) = do
  checkTypeVars "hiding class declaration" [clsvar]
  cx' <- checkClosedContext [clsvar] cx
  checkSimpleContext cx'
  return $ HidingClassDecl p cx' qcls k clsvar
checkIDecl (IClassDecl p cx qcls k clsvar ms hs) = do
  checkTypeVars "class declaration" [clsvar]
  cx' <- checkClosedContext [clsvar] cx
  checkSimpleContext cx'
  ms' <- mapM (checkIMethodDecl clsvar) ms
  checkHidden (errNoElement "method" "class") qcls (map imethod ms') hs
  return $ IClassDecl p cx' qcls k clsvar ms' hs
checkIDecl (IInstanceDecl p cx qcls inst m) = do
  checkClass qcls
  QualTypeExpr cx' inst' <- checkQualType $ QualTypeExpr cx inst
  checkSimpleContext cx'
  checkInstanceType p inst'
  return $ IInstanceDecl p cx' qcls inst' m

checkHiddenType :: QualIdent -> [Ident] -> [Ident] -> ISC ()
checkHiddenType = checkHidden $ errNoElement "constructor or label" "type"

checkHidden :: (QualIdent -> Ident -> Message) -> QualIdent -> [Ident]
            -> [Ident] -> ISC ()
checkHidden err tc csls hs =
  mapM_ (report . err tc) $ nub $ filter (`notElem` csls) hs

checkTypeLhs :: [Ident] -> ISC ()
checkTypeLhs = checkTypeVars "left hand side of type declaration"

checkExistVars :: [Ident] -> ISC ()
checkExistVars = checkTypeVars "list of existentially quantified type variables"

checkTypeVars :: String -> [Ident] -> ISC ()
checkTypeVars what tvs = do
  tyEnv <- getTypeEnv
  let (tcs, tvs') = partition isTypeConstrOrClass tvs
      isTypeConstrOrClass tv = not (null (lookupTypeKind tv tyEnv))
  mapM_ (report . flip errNoVariable what)       (nub tcs)
  mapM_ (report . flip errNonLinear what . head) (findMultiples tvs')

checkConstrDecl :: [Ident] -> ConstrDecl -> ISC ConstrDecl
checkConstrDecl tvs (ConstrDecl p evs c tys) = do
  checkExistVars evs
  liftM (ConstrDecl p evs c) (mapM (checkClosedType tvs') tys)
  where tvs' = evs ++ tvs
checkConstrDecl tvs (ConOpDecl p evs ty1 op ty2) = do
  checkExistVars evs
  liftM2 (\t1 t2 -> ConOpDecl p evs t1 op t2)
         (checkClosedType tvs' ty1)
         (checkClosedType tvs' ty2)
  where tvs' = evs ++ tvs
checkConstrDecl tvs (RecordDecl p evs c fs) = do
  checkExistVars evs
  liftM (RecordDecl p evs c) (mapM (checkFieldDecl tvs') fs)
  where tvs' = evs ++ tvs

checkFieldDecl :: [Ident] -> FieldDecl -> ISC FieldDecl
checkFieldDecl tvs (FieldDecl p ls ty) =
  liftM (FieldDecl p ls) (checkClosedType tvs ty)

checkNewConstrDecl :: [Ident] -> NewConstrDecl -> ISC NewConstrDecl
checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
  checkExistVars evs
  liftM (NewConstrDecl p evs c) (checkClosedType tvs' ty)
  where tvs' = evs ++ tvs
checkNewConstrDecl tvs (NewRecordDecl p evs c (l,ty)) = do
  checkExistVars evs
  ty' <- checkClosedType tvs' ty
  return $ NewRecordDecl p evs c (l,ty')
  where tvs' = evs ++ tvs

checkSimpleContext :: Context -> ISC ()
checkSimpleContext = mapM_ checkSimpleConstraint

checkSimpleConstraint :: Constraint -> ISC ()
checkSimpleConstraint c@(Constraint _ ty) =
  unless (isVariableType ty) $ report $ errIllegalSimpleConstraint c

checkIMethodDecl :: Ident -> IMethodDecl -> ISC IMethodDecl
checkIMethodDecl tv (IMethodDecl p f qty) = do
  qty' <- checkQualType qty
  unless (tv `elem` fv qty') $ report $ errAmbiguousType p tv
  let QualTypeExpr cx _ = qty'
  when (tv `elem` fv cx) $ report $ errConstrainedClassVariable p tv
  return $ IMethodDecl p f qty'

checkInstanceType :: Position -> InstanceType -> ISC ()
checkInstanceType p inst = do
  tEnv <- getTypeEnv
  unless (isSimpleType inst &&
    not (isTypeSyn (typeConstr inst) tEnv) &&
    null (filter isAnonId $ typeVars inst) &&
    isNothing (findDouble $ fv inst)) $
      report $ errIllegalInstanceType p inst

checkQualType :: QualTypeExpr -> ISC QualTypeExpr
checkQualType (QualTypeExpr cx ty) = do
  ty' <- checkType ty
  cx' <- checkClosedContext (fv ty') cx
  return $ QualTypeExpr cx' ty'

checkClosedContext :: [Ident] -> Context -> ISC Context
checkClosedContext tvs cx = do
  cx' <- checkContext cx
  mapM_ (\(Constraint _ ty) -> checkClosed tvs ty) cx'
  return cx'

checkContext :: Context -> ISC Context
checkContext = mapM checkConstraint

checkConstraint :: Constraint -> ISC Constraint
checkConstraint (Constraint qcls ty) = do
  checkClass qcls
  Constraint qcls <$> checkType ty

checkClass :: QualIdent -> ISC ()
checkClass qcls = do
  tEnv <- getTypeEnv
  case qualLookupTypeKind qcls tEnv of
    [] -> report $ errUndefinedClass qcls
    [Class _ _] -> return ()
    [_] -> report $ errUndefinedClass qcls
    _ -> internalError $ "Checks.InterfaceSyntaxCheck.checkClass: " ++
           "ambiguous identifier " ++ show qcls

checkClosedType :: [Ident] -> TypeExpr -> ISC TypeExpr
checkClosedType tvs ty = do
  ty' <- checkType ty
  checkClosed tvs ty'
  return ty'

checkType :: TypeExpr -> ISC TypeExpr
checkType (ConstructorType tc) = checkTypeConstructor tc
checkType (ApplyType  ty1 ty2) = liftM2 ApplyType (checkType ty1) (checkType ty2)
checkType (VariableType    tv) = checkType $ ConstructorType (qualify tv)
checkType (TupleType      tys) = liftM TupleType (mapM checkType tys)
checkType (ListType        ty) = liftM ListType (checkType ty)
checkType (ArrowType  ty1 ty2) = liftM2 ArrowType (checkType ty1) (checkType ty2)
checkType (ParenType       ty) = liftM ParenType (checkType ty)

checkClosed :: [Ident] -> TypeExpr -> ISC ()
checkClosed _   (ConstructorType _) = return ()
checkClosed tvs (ApplyType ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (VariableType   tv) =
  when (isAnonId tv || tv `notElem` tvs) $ report $ errUnboundVariable tv
checkClosed tvs (TupleType     tys) = mapM_ (checkClosed tvs) tys
checkClosed tvs (ListType       ty) = checkClosed tvs ty
checkClosed tvs (ArrowType ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (ParenType      ty) = checkClosed tvs ty

checkTypeConstructor :: QualIdent -> ISC TypeExpr
checkTypeConstructor tc = do
  tyEnv <- getTypeEnv
  case qualLookupTypeKind tc tyEnv of
    [] | not (isQualified tc) -> return $ VariableType $ unqualify tc
       | otherwise            -> do
          report $ errUndefinedType tc
          return $ ConstructorType tc
    [Data _ _] -> return $ ConstructorType tc
    [Alias  _] -> do
                  report $ errBadTypeSynonym tc
                  return $ ConstructorType tc
    _          ->
      internalError "Checks.InterfaceSyntaxCheck.checkTypeConstructor"

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

typeConstr :: TypeExpr -> QualIdent
typeConstr (ConstructorType   tc) = tc
typeConstr (ApplyType       ty _) = typeConstr ty
typeConstr (VariableType       _) =
  internalError "Checks.InterfaceSyntaxCheck.typeConstr: variable type"
typeConstr (TupleType        tys) = qTupleId (length tys)
typeConstr (ListType           _) = qListId
typeConstr (ArrowType        _ _) = qArrowId
typeConstr (ParenType         ty) = typeConstr ty

typeVars :: TypeExpr -> [Ident]
typeVars (ConstructorType       _) = []
typeVars (ApplyType       ty1 ty2) = typeVars ty1 ++ typeVars ty2
typeVars (VariableType         tv) = [tv]
typeVars (TupleType           tys) = concatMap typeVars tys
typeVars (ListType             ty) = typeVars ty
typeVars (ArrowType       ty1 ty2) = typeVars ty1 ++ typeVars ty2
typeVars (ParenType            ty) = typeVars ty

isTypeSyn :: QualIdent -> TypeEnv -> Bool
isTypeSyn tc tEnv = case qualLookupTypeKind tc tEnv of
  [Alias _] -> True
  _ -> False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUndefined :: String -> QualIdent -> Message
errUndefined what qident = posMessage qident $ hsep $ map text
  ["Undefined", what, qualName qident]

errUndefinedClass :: QualIdent -> Message
errUndefinedClass = errUndefined "class"

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "type"

errAmbiguousType :: Position -> Ident -> Message
errAmbiguousType p ident = posMessage p $ hsep $ map text
  [ "Method type does not mention class variable", idName ident ]

errConstrainedClassVariable :: Position -> Ident -> Message
errConstrainedClassVariable p ident = posMessage p $ hsep $ map text
  [ "Method context must not constrain class variable", idName ident ]

errNonLinear :: Ident -> String -> Message
errNonLinear tv what = posMessage tv $ hsep $ map text
  [ "Type variable", escName tv, "occurs more than once in", what ]

errNoVariable :: Ident -> String -> Message
errNoVariable tv what = posMessage tv $ hsep $ map text
  [ "Type constructor or type class identifier", escName tv, "used in", what ]

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = posMessage tv $
  text "Undefined type variable" <+> text (escName tv)

errBadTypeSynonym :: QualIdent -> Message
errBadTypeSynonym tc = posMessage tc $ text "Synonym type"
                    <+> text (qualName tc) <+> text "in interface"

errNoElement :: String -> String -> QualIdent -> Ident -> Message
errNoElement what for tc x = posMessage tc $ hsep $ map text
  [ "Hidden", what, escName x, "is not defined for", for, qualName tc ]

errIllegalSimpleConstraint :: Constraint -> Message
errIllegalSimpleConstraint c@(Constraint qcls _) = posMessage qcls $ vcat
  [ text "Illegal class constraint" <+> ppConstraint c
  , text "Constraints in class and instance declarations must be of"
  , text "the form C u, where C is a type class and u is a type variable."
  ]

errIllegalInstanceType :: Position -> InstanceType -> Message
errIllegalInstanceType p inst = posMessage p $ vcat
  [ text "Illegal instance type" <+> ppInstanceType inst
  , text "The instance type must be of the form (T u_1 ... u_n),"
  , text "where T is not a type synonym and u_1, ..., u_n are"
  , text "mutually distinct, non-anonymous type variables."
  ]
