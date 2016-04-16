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

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Expr (fv)
import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Utils (findMultiples)

import Env.TypeConstructor (TCEnv)
import Env.TypeEnv

-- In order to check type constructor applications, the compiler
-- maintains an environment containing all known type constructors and
-- type classes. The function 'typeSyntaxCheck' expects a type constructor
-- environment that is already initialized with the imported type constructors
-- and type classes. The type constructor environment is converted to a type
-- identifier environment, before all locally defined type constructors and
-- type classes are added to this environment and the declarations are checked
-- within this environment.

typeSyntaxCheck :: TCEnv -> Module -> (Module, [Message])
typeSyntaxCheck tcEnv mdl@(Module _ m _ _ ds) =
  case findMultiples $ map getIdent tcds of
    [] -> runTSCM (checkModule mdl) state
    tss -> (mdl, map errMultipleDeclaration tss)
  where
    tcds = filter isTypeOrClassDecl ds
    tEnv' = foldr (bindType m) (fmap toTypeKind tcEnv) tcds
    state = TSCState tEnv' []

-- Type Syntax Check Monad
type TSCM = S.State TSCState

-- |Internal state of the Type Syntax Check
data TSCState = TSCState
  { typeEnv     :: TypeEnv
  , errors      :: [Message]
  }

runTSCM :: TSCM a -> TSCState -> (a, [Message])
runTSCM kcm s = let (a, s') = S.runState kcm s in (a, reverse $ errors s')

getTypeEnv :: TSCM TypeEnv
getTypeEnv = S.gets typeEnv

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
    ms = maybe [] (concatMap methods) ds
bindType _ _ = id

-- When type declarations are checked, the compiler will allow anonymous
-- type variables on the left hand side of the declaration, but not on
-- the right hand side. Function and pattern declarations must be
-- traversed because they can contain local type signatures.

checkModule :: Module -> TSCM Module
checkModule (Module ps m es is ds) = Module ps m es is <$> mapM checkDecl ds

checkDecl :: Decl -> TSCM Decl
checkDecl (DataDecl p tc tvs cs) = do
  checkTypeVars tvs "left hand side of data declaration"
  cs'  <- mapM (checkConstrDecl tvs) cs
  return $ DataDecl p tc tvs cs'
checkDecl (NewtypeDecl p tc tvs nc) = do
  checkTypeVars tvs "left hand side of newtype declaration"
  nc'  <- checkNewConstrDecl tvs nc
  return $ NewtypeDecl p tc tvs nc'
checkDecl (TypeDecl p tc tvs ty) = do
  checkTypeVars tvs "left hand side of type declaration"
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
checkDecl (ClassDecl p scx cls clsvar ds) = do
  checkTypeVars [clsvar] "class declaration"
  maybe ok (checkClosedSimpleContext [clsvar]) scx
  ds' <- traverse (mapM checkDecl) ds
  maybe ok (mapM_ (checkClassMethod clsvar)) ds
  return $ ClassDecl p scx cls clsvar ds'
checkDecl (InstanceDecl p scx cls inst ds) = do
  -- TODO: check simple context
  -- TODO: check instance type
  ds' <- traverse (mapM checkDecl) ds
  return $ InstanceDecl p scx cls inst ds'
checkDecl d = return d

checkConstrDecl :: [Ident] -> ConstrDecl -> TSCM ConstrDecl
checkConstrDecl tvs (ConstrDecl p evs c tys) = do
  checkTypeVars evs ""
  tys' <- mapM (checkClosedType (evs ++ tvs)) tys
  return $ ConstrDecl p evs c tys'
checkConstrDecl tvs (ConOpDecl p evs ty1 op ty2) = do
  checkTypeVars evs ""
  let tvs' = evs ++ tvs
  ty1' <- checkClosedType tvs' ty1
  ty2' <- checkClosedType tvs' ty2
  return $ ConOpDecl p evs ty1' op ty2'
checkConstrDecl tvs (RecordDecl p evs c fs) = do
  checkTypeVars evs ""
  fs'  <- mapM (checkFieldDecl (evs ++ tvs)) fs
  return $ RecordDecl p evs c fs'

checkFieldDecl :: [Ident] -> FieldDecl -> TSCM FieldDecl
checkFieldDecl tvs (FieldDecl p ls ty) =
  FieldDecl p ls <$> checkClosedType tvs ty

checkNewConstrDecl :: [Ident] -> NewConstrDecl -> TSCM NewConstrDecl
checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
  checkTypeVars evs ""
  ty'  <- checkClosedType (evs ++ tvs) ty
  return $ NewConstrDecl p evs c ty'
checkNewConstrDecl tvs (NewRecordDecl p evs c (l, ty)) = do
  checkTypeVars evs ""
  ty'  <- checkClosedType (evs ++ tvs) ty
  return $ NewRecordDecl p evs c (l, ty')

checkClassMethod :: Ident -> Decl -> TSCM ()
checkClassMethod tv (TypeSig _ _ ty) =
  unless (tv `elem` fv ty) $ report $ errAmbiguousType tv
  --TODO: check that the class variable is not constrained by the method's context
checkClassMethod _ _ = ok

-- |Check a list of type variables, e.g., the left-hand-side of a type
-- declaration or class variables in a class declaration, for
-- * Anonymous type variables are allowed
-- * only type variables (no type constructors)
-- * linearity
checkTypeVars :: [Ident] -> String -> TSCM ()
checkTypeVars []         _    = ok
checkTypeVars (tv : tvs) what = do
  unless (isAnonId tv) $ do
    isTyCons <- (not . null . lookupTypeKind tv) <$> getTypeEnv
    when isTyCons $ report $ errNoVariable tv what
    when (tv `elem` tvs) $ report $ errNonLinear tv what
  checkTypeVars tvs what

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

-- The context of a class or instance declaration is only allowed to
-- constrain the class variables.

checkClosedSimpleContext :: [Ident] -> SimpleContext -> TSCM ()
checkClosedSimpleContext tvs (SimpleContext sc) =
  checkClosedSimpleConstraint tvs sc
checkClosedSimpleContext tvs (ParenSimpleContext scs) =
  mapM_ (checkClosedSimpleConstraint tvs) scs

checkClosedSimpleConstraint :: [Ident] -> SimpleConstraint -> TSCM ()
checkClosedSimpleConstraint tvs (SimpleConstraint (_, tv)) =
  checkClosed tvs (VariableType tv)

-- The parser cannot distinguish unqualified nullary type constructors
-- and type variables. Therefore, if the compiler finds an unbound
-- identifier in a position where a type variable is admissible, it will
-- interpret the identifier as such.

checkClosedType :: [Ident] -> TypeExpr -> TSCM TypeExpr
checkClosedType tvs ty = do
  ty' <- checkType ty
  --mapM_ (report . errUnboundVariable) (nub (filter (\tv -> isAnonId tv || tv `notElem` tvs) (fv ty')))
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
    tis -> report (errAmbiguousIdent tc $ map origName tis) >> return c
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

errUndefinedType :: QualIdent -> Message
errUndefinedType tc = posMessage tc $ hsep $ map text
  ["Undefined type", qualName tc]

errAmbiguousIdent :: QualIdent -> [QualIdent] -> Message
errAmbiguousIdent qident qidents = posMessage qident $
  text "Ambiguous identifier" <+> text (escQualName qident) $+$
   text "It could refer to:" $+$ nest 2 (vcat (map (text . qualName) qidents))

errAmbiguousType :: Ident -> Message
errAmbiguousType ident = posMessage ident $ hsep $ map text
  ["Method type does not mention class variable", idName ident]

errNonLinear :: Ident -> String -> Message
errNonLinear tv what = posMessage tv $ hsep $ map text $
  ["Type variable", idName tv, "occurs more than once"] ++
    if null what then [] else ["in", what]

errNoVariable :: Ident -> String -> Message
errNoVariable tv what = posMessage tv $ hsep $ map text $
  ["Type constructor", idName tv, "used"] ++
    if null what then [] else ["in", what]

errUnboundVariable :: Ident -> Message
errUnboundVariable tv = posMessage tv $ hsep $ map text
  ["Unbound type variable", idName tv]
