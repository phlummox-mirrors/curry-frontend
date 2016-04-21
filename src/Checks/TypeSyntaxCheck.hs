{- |
    Module      :  $Header$
    Description :  Checks type syntax
    Copyright   :  (c)        2016 Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After the source file has been parsed and all modules have been
   imported, the compiler first checks all type definitions and
   signatures. In particular, this module disambiguates nullary type
   constructors and type variables, which -- in contrast to Haskell -- is
   not possible on purely syntactic criteria. In addition it is checked
   that all type constructors and type variables occurring on the right
   hand side of a type declaration are actually defined and no identifier
   is defined more than once.
-}
{-# LANGUAGE CPP #-}
module Checks.TypeSyntaxCheck (typeSyntaxCheck) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>))
#endif
import           Control.Monad            (unless, when)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import           Data.List                (nub)
import           Data.Maybe               (isNothing)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.Expr (fv)
import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Utils (findMultiples, findDouble)

import Env.TypeConstructor (TCEnv)
import Env.TypeEnv

import CompilerOpts

-- In order to check type constructor applications, the compiler
-- maintains an environment containing all known type constructors and
-- type classes. The function 'typeSyntaxCheck' expects a type constructor
-- environment that is already initialized with the imported type constructors
-- and type classes. The type constructor environment is converted to a type
-- identifier environment, before all locally defined type constructors and
-- type classes are added to this environment and the declarations are checked
-- within this environment.

typeSyntaxCheck :: [KnownExtension] -> TCEnv -> Module
                -> ((Module, [KnownExtension]), [Message])
typeSyntaxCheck exts tcEnv mdl@(Module _ m _ _ ds) =
  case findMultiples $ map getIdent tcds of
    [] -> runTSCM (checkModule mdl) state
    tss -> ((mdl, exts), map errMultipleDeclaration tss)
  where
    tcds = filter isTypeOrClassDecl ds
    tEnv = foldr (bindType m) (fmap toTypeKind tcEnv) tcds
    state = TSCState tEnv exts []

-- Type Syntax Check Monad
type TSCM = S.State TSCState

-- |Internal state of the Type Syntax Check
data TSCState = TSCState
  { typeEnv     :: TypeEnv
  , extensions  :: [KnownExtension]
  , errors      :: [Message]
  }

runTSCM :: TSCM a -> TSCState -> (a, [Message])
runTSCM kcm s = let (a, s') = S.runState kcm s in (a, reverse $ errors s')

getTypeEnv :: TSCM TypeEnv
getTypeEnv = S.gets typeEnv

hasExtension :: KnownExtension -> TSCM Bool
hasExtension ext = S.gets (elem ext . extensions)

enableExtension :: KnownExtension -> TSCM ()
enableExtension e = S.modify $ \s -> s { extensions = e : extensions s }

getExtensions :: TSCM [KnownExtension]
getExtensions = S.gets extensions

report :: Message -> TSCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: TSCM ()
ok = return ()

bindType :: ModuleIdent -> Decl -> TypeEnv -> TypeEnv
bindType m (DataDecl _ tc _ cs) = bindTypeKind m tc (Data qtc ids)
  where
    qtc = qualifyWith m tc
    ids = map constrId cs ++ nub (concatMap recordLabels cs)
bindType m (NewtypeDecl _ tc _ nc) = bindTypeKind m tc (Data qtc ids)
  where
    qtc = qualifyWith m tc
    ids = nconstrId nc : nrecordLabels nc
bindType m (TypeDecl _ tc _ _) = bindTypeKind m tc (Alias qtc)
  where
    qtc = qualifyWith m tc
bindType m (ClassDecl _ _ cls _ ds) = bindTypeKind m cls (Class qcls ms)
  where
    qcls = qualifyWith m cls
    ms = concatMap methods ds
bindType _ _ = id

-- When type declarations are checked, the compiler will allow anonymous
-- type variables on the left hand side of the declaration, but not on
-- the right hand side. Function and pattern declarations must be
-- traversed because they can contain local type signatures.

checkModule :: Module -> TSCM (Module, [KnownExtension])
checkModule (Module ps m es is ds) = do
  ds' <- mapM checkDecl ds
  exts <- getExtensions
  return (Module ps m es is ds', exts)

checkDecl :: Decl -> TSCM Decl
checkDecl (DataDecl p tc tvs cs) = do
  checkTypeLhs tvs
  cs'  <- mapM (checkConstrDecl tvs) cs
  return $ DataDecl p tc tvs cs'
checkDecl (NewtypeDecl p tc tvs nc) = do
  checkTypeLhs tvs
  nc'  <- checkNewConstrDecl tvs nc
  return $ NewtypeDecl p tc tvs nc'
checkDecl (TypeDecl p tc tvs ty) = do
  checkTypeLhs tvs
  ty'  <- checkClosedType tvs ty
  return $ TypeDecl p tc tvs ty'
checkDecl (TypeSig p vs ty) =
  TypeSig p vs <$> checkType ty
checkDecl (FunctionDecl p f eqs) =
  FunctionDecl p f <$> mapM checkEquation eqs
checkDecl (PatternDecl p t rhs) =
  PatternDecl p t <$> checkRhs rhs
checkDecl (ForeignDecl p cc ie f ty) =
  ForeignDecl p cc ie f <$> checkType ty
checkDecl (ClassDecl p cx cls clsvar ds) = do
  checkTypeVars "class declaration" [clsvar]
  cx' <- checkClosedContext [clsvar] cx
  checkSimpleContext cx'
  ds' <- mapM checkDecl ds
  mapM_ (checkClassMethod clsvar) ds'
  return $ ClassDecl p cx' cls clsvar ds'
checkDecl (InstanceDecl p cx qcls inst ds) = do
  checkClass qcls
  cx' <- checkContext cx
  checkSimpleContext cx'
  inst' <- checkInstanceType p inst
  --TODO: check context and instance type as qualified type
  InstanceDecl p cx' qcls inst' <$> mapM checkDecl ds
checkDecl d = return d

checkConstrDecl :: [Ident] -> ConstrDecl -> TSCM ConstrDecl
checkConstrDecl tvs (ConstrDecl p evs c tys) = do
  checkExistVars evs
  tys' <- mapM (checkClosedType (evs ++ tvs)) tys
  return $ ConstrDecl p evs c tys'
checkConstrDecl tvs (ConOpDecl p evs ty1 op ty2) = do
  checkExistVars evs
  let tvs' = evs ++ tvs
  ty1' <- checkClosedType tvs' ty1
  ty2' <- checkClosedType tvs' ty2
  return $ ConOpDecl p evs ty1' op ty2'
checkConstrDecl tvs (RecordDecl p evs c fs) = do
  checkExistVars evs
  fs'  <- mapM (checkFieldDecl (evs ++ tvs)) fs
  return $ RecordDecl p evs c fs'

checkFieldDecl :: [Ident] -> FieldDecl -> TSCM FieldDecl
checkFieldDecl tvs (FieldDecl p ls ty) =
  FieldDecl p ls <$> checkClosedType tvs ty

checkNewConstrDecl :: [Ident] -> NewConstrDecl -> TSCM NewConstrDecl
checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
  checkExistVars evs
  ty'  <- checkClosedType (evs ++ tvs) ty
  return $ NewConstrDecl p evs c ty'
checkNewConstrDecl tvs (NewRecordDecl p evs c (l, ty)) = do
  checkExistVars evs
  ty'  <- checkClosedType (evs ++ tvs) ty
  return $ NewRecordDecl p evs c (l, ty')

checkClass :: QualIdent -> TSCM ()
checkClass qcls = do
  tEnv <- getTypeEnv
  case qualLookupTypeKind qcls tEnv of
    [] -> report $ errUndefinedClass qcls
    [Class _ _] -> ok
    [_] -> report $ errUndefinedClass qcls
    tks -> report $ errAmbiguousIdent qcls $ map origName tks

checkClosedContext :: [Ident] -> Context -> TSCM Context
checkClosedContext tvs cx = do
  cx' <- checkContext cx
  mapM_ (\(Constraint _ ty) -> checkClosed tvs ty) cx'
  return cx'

checkContext :: Context -> TSCM Context
checkContext = mapM checkConstraint

checkConstraint :: Constraint -> TSCM Constraint
checkConstraint (Constraint qcls ty) = do
  checkClass qcls
  Constraint qcls <$> checkType ty

checkSimpleContext :: Context -> TSCM ()
checkSimpleContext = mapM_ checkSimpleConstraint

checkSimpleConstraint :: Constraint -> TSCM ()
checkSimpleConstraint c@(Constraint _ ty) =
  unless (isVariableType ty) $ report $ errIllegalSimpleConstraint c

checkClassMethod :: Ident -> Decl -> TSCM ()
checkClassMethod tv (TypeSig _ _ ty) =
  unless (tv `elem` fv ty) $ report $ errAmbiguousType tv
  --TODO: check that the class variable is not constrained by the method's context
checkClassMethod _ _ = ok

checkInstanceType :: Position -> InstanceType -> TSCM InstanceType
checkInstanceType p inst = do
  tEnv <- getTypeEnv
  inst' <- checkType inst
  unless (isSimpleType inst' &&
    not (isTypeSyn (typeConstr inst) tEnv) &&
    null (filter isAnonId $ typeVars inst') &&
    isNothing (findDouble $ fv inst')) $
      report $ errIllegalInstanceType p inst'
  return inst'

checkTypeLhs :: [Ident] -> TSCM ()
checkTypeLhs = checkTypeVars "left hand side of type declaration"

checkExistVars :: [Ident] -> TSCM ()
checkExistVars evs = do
  unless (null evs) $ checkUsedExtension (idPosition $ head evs)
    "Existentially quantified types" ExistentialQuantification
  checkTypeVars "list of existentially quantified type variables" evs

-- |Checks a list of type variables for
-- * Anonymous type variables are allowed
-- * only type variables (no type constructors)
-- * linearity
checkTypeVars :: String -> [Ident] -> TSCM ()
checkTypeVars _    []         = ok
checkTypeVars what (tv : tvs) = do
  unless (isAnonId tv) $ do
    isTyCons <- (not . null . lookupTypeKind tv) <$> getTypeEnv
    when isTyCons $ report $ errNoVariable tv what
    when (tv `elem` tvs) $ report $ errNonLinear tv what
  checkTypeVars what tvs

-- Checking expressions is rather straight forward. The compiler must
-- only traverse the structure of expressions in order to find local
-- declaration groups.

checkEquation :: Equation -> TSCM Equation
checkEquation (Equation p lhs rhs) = Equation p lhs <$> checkRhs rhs

checkRhs :: Rhs -> TSCM Rhs
checkRhs (SimpleRhs p e ds) = SimpleRhs p <$> checkExpr e <*> mapM checkDecl ds
checkRhs (GuardedRhs es ds) = GuardedRhs  <$> mapM checkCondExpr es
                                          <*> mapM checkDecl ds

checkCondExpr :: CondExpr -> TSCM CondExpr
checkCondExpr (CondExpr p g e) = CondExpr p <$> checkExpr g <*> checkExpr e

checkExpr :: Expression -> TSCM Expression
checkExpr l@(Literal             _) = return l
checkExpr v@(Variable            _) = return v
checkExpr c@(Constructor         _) = return c
checkExpr (Paren                 e) = Paren <$> checkExpr e
checkExpr (Typed              e ty) = Typed <$> checkExpr e <*> checkType ty
checkExpr (Record             c fs) = Record c <$> mapM checkFieldExpr fs
checkExpr (RecordUpdate       e fs) = RecordUpdate <$> checkExpr e
                                                   <*> mapM checkFieldExpr fs
checkExpr (Tuple              p es) = Tuple p <$> mapM checkExpr es
checkExpr (List               p es) = List  p <$> mapM checkExpr es
checkExpr (ListCompr        p e qs) = ListCompr p <$> checkExpr e
                                                 <*> mapM checkStmt qs
checkExpr (EnumFrom              e) = EnumFrom <$> checkExpr e
checkExpr (EnumFromThen      e1 e2) = EnumFromThen <$> checkExpr e1
                                                   <*> checkExpr e2
checkExpr (EnumFromTo        e1 e2) = EnumFromTo <$> checkExpr e1
                                                 <*> checkExpr e2
checkExpr (EnumFromThenTo e1 e2 e3) = EnumFromThenTo <$> checkExpr e1
                                                     <*> checkExpr e2
                                                     <*> checkExpr e3
checkExpr (UnaryMinus         op e) = UnaryMinus op <$> checkExpr e
checkExpr (Apply             e1 e2) = Apply <$> checkExpr e1 <*> checkExpr e2
checkExpr (InfixApply     e1 op e2) = InfixApply <$> checkExpr e1
                                                 <*> return op
                                                 <*> checkExpr e2
checkExpr (LeftSection        e op) = flip LeftSection op <$> checkExpr e
checkExpr (RightSection       op e) = RightSection op <$> checkExpr e
checkExpr (Lambda           r ts e) = Lambda r ts <$> checkExpr e
checkExpr (Let                ds e) = Let <$> mapM checkDecl ds <*> checkExpr e
checkExpr (Do                sts e) = Do <$> mapM checkStmt sts <*> checkExpr e
checkExpr (IfThenElse   r e1 e2 e3) = IfThenElse r <$> checkExpr e1
                                                   <*> checkExpr e2
                                                   <*> checkExpr e3
checkExpr (Case        r ct e alts) = Case r ct <$> checkExpr e
                                                <*> mapM checkAlt alts

checkStmt :: Statement -> TSCM Statement
checkStmt (StmtExpr   p e) = StmtExpr p <$> checkExpr e
checkStmt (StmtBind p t e) = StmtBind p t <$> checkExpr e
checkStmt (StmtDecl    ds) = StmtDecl <$> mapM checkDecl ds

checkAlt :: Alt -> TSCM Alt
checkAlt (Alt p t rhs) = Alt p t <$> checkRhs rhs

checkFieldExpr :: Field Expression -> TSCM (Field Expression)
checkFieldExpr (Field p l e) = Field p l <$> checkExpr e

-- The parser cannot distinguish unqualified nullary type constructors
-- and type variables. Therefore, if the compiler finds an unbound
-- identifier in a position where a type variable is admissible, it will
-- interpret the identifier as such.

checkClosedType :: [Ident] -> TypeExpr -> TSCM TypeExpr
checkClosedType tvs ty = do
  ty' <- checkType ty
  checkClosed tvs ty'
  return ty'

checkType :: TypeExpr -> TSCM TypeExpr
checkType c@(ConstructorType tc) = do
  tEnv <- getTypeEnv
  case qualLookupTypeKind tc tEnv of
    []
      | not (isQualified tc) -> return $ VariableType $ unqualify tc
      | otherwise -> report (errUndefinedType tc) >> return c
    [Class _ _] -> report (errUndefinedType tc) >> return c
    [_] -> return c
    tks -> report (errAmbiguousIdent tc $ map origName tks) >> return c
checkType (ApplyType ty1 ty2) = ApplyType  <$> checkType ty1 <*> checkType ty2
checkType v@(VariableType tv)
  | isAnonId tv = return v
  | otherwise   = checkType $ ConstructorType (qualify tv)
checkType (TupleType     tys) = TupleType  <$> mapM checkType tys
checkType (ListType       ty) = ListType   <$> checkType ty
checkType (ArrowType ty1 ty2) = ArrowType  <$> checkType ty1 <*> checkType ty2
checkType (ParenType      ty) = ParenType  <$> checkType ty

checkClosed :: [Ident] -> TypeExpr -> TSCM ()
checkClosed _   (ConstructorType _) = ok
checkClosed tvs (ApplyType ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (VariableType   tv) =
  when (isAnonId tv || tv `notElem` tvs) $ report $ errUnboundVariable tv
checkClosed tvs (TupleType     tys) = mapM_ (checkClosed tvs) tys
checkClosed tvs (ListType       ty) = checkClosed tvs ty
checkClosed tvs (ArrowType ty1 ty2) = mapM_ (checkClosed tvs) [ty1, ty2]
checkClosed tvs (ParenType      ty) = checkClosed tvs ty

checkUsedExtension :: Position -> String -> KnownExtension -> TSCM ()
checkUsedExtension pos msg ext = do
  enabled <- hasExtension ext
  unless enabled $ do
    report $ errMissingLanguageExtension pos msg ext
    enableExtension ext

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

getIdent :: Decl -> Ident
getIdent (DataDecl       _ tc _ _) = tc
getIdent (NewtypeDecl    _ tc _ _) = tc
getIdent (TypeDecl       _ tc _ _) = tc
getIdent (ClassDecl   _ _ cls _ _) = cls
getIdent _                         =
  internalError "TypeSyntaxCheck.getIdent: no type or class declaration"

typeConstr :: TypeExpr -> QualIdent
typeConstr (ConstructorType   tc) = tc
typeConstr (ApplyType       ty _) = typeConstr ty
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

errMultipleDeclaration :: [Ident] -> Message
errMultipleDeclaration []     = internalError
  "TypeSyntaxCheck.errMultipleDeclaration: empty list"
errMultipleDeclaration (i:is) = posMessage i $
  text "Multiple declarations of" <+> text (escName i) <+> text "at:" $+$
    nest 2 (vcat (map showPos (i:is)))
  where
    showPos = text . showLine . idPosition

errMissingLanguageExtension :: Position -> String -> KnownExtension -> Message
errMissingLanguageExtension p what ext = posMessage p $
  text what <+> text "are not supported in standard Curry." $+$
  nest 2 (text "Use flag -X" <+> text (show ext)
          <+> text "to enable this extension.")

errUndefined :: String -> QualIdent -> Message
errUndefined what qident = posMessage qident $ hsep $ map text
  ["Undefined", what, qualName qident]

errUndefinedClass :: QualIdent -> Message
errUndefinedClass = errUndefined "class"

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "type"

errAmbiguousIdent :: QualIdent -> [QualIdent] -> Message
errAmbiguousIdent qident qidents = posMessage qident $
  text "Ambiguous identifier" <+> text (escQualName qident) $+$
    text "It could refer to:" $+$ nest 2 (vcat (map (text . qualName) qidents))

errAmbiguousType :: Ident -> Message
errAmbiguousType ident = posMessage ident $ hsep $ map text
  [ "Method type does not mention class variable", idName ident ]

errNonLinear :: Ident -> String -> Message
errNonLinear tv what = posMessage tv $ hsep $ map text
  [ "Type variable", idName tv, "occurs more than once in", what ]

errNoVariable :: Ident -> String -> Message
errNoVariable tv what = posMessage tv $ hsep $ map text $
  [ "Type constructor", idName tv, "used in", what ]

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = posMessage tv $ hsep $ map text
  [ "Unbound type variable", idName tv ]

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
  , text "mutually distinct type variables."
  ]
