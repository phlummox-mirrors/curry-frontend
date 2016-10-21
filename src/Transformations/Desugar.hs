{- |
  Module      :  $Header$
  Description :  Desugaring Curry Expressions
  Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                                 Martin Engelke
                     2011 - 2015 Björn Peemöller
                     2015        Jan Tikovsky
                     2016        Finn Teegen
  License     :  OtherLicense

  Maintainer  :  bjp@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  The desugaring pass removes all syntactic sugar from the module.
  In particular, the output of the desugarer will have the following
  properties.

  * No guarded right hand sides occur in equations, pattern declarations,
    and case alternatives. In addition, the declaration lists (`where`-blocks)
    of the right hand sides are empty; local declarations are transformed
    into let expressions.

  * Patterns in equations and case alternatives are composed only of
    - literals,
    - variables,
    - constructor applications, and
    - as patterns applied to literals or constructor applications.

  * Expressions are composed only of
    - literals,
    - variables,
    - constructors,
    - (binary) applications,
    - case expressions,
    - let expressions, and
    - expressions with a type signature.

  * Applications 'N x' in patterns and expressions, where 'N' is a
    newtype constructor, are replaced by a 'x'. Note that neither the
    newtype declaration itself nor partial applications of newtype
    constructors are changed.
    It were possible to replace partial applications of newtype constructor
    by 'Prelude.id'.
    However, our solution yields a more accurate output when the result
    of a computation includes partial applications.

  * Functional patterns are replaced by variables and are integrated
    in a guarded right hand side using the (=:<=) operator.

  * Records are transformed into ordinary data types by removing the fields.
    Record construction and pattern matching are represented using solely the
    record constructor. Record selections are represented using selector
    functions which are generated for each record declaration, and record
    updated are represented using case-expressions that perform the update.

  * The type environment will be extended by new function declarations for:
    - Record selections, and
    - Converted lambda expressions.

  As we are going to insert references to real prelude entities,
  all names must be properly qualified before calling this module.
-}
{-# LANGUAGE CPP #-}
module Transformations.Desugar (desugar) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Arrow              (first, second)
import           Control.Monad              (liftM2, mplus)
import           Control.Monad.Extra        (concatMapM)
import           Control.Monad.ListM        (mapAccumM)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List                  ( (\\), elemIndex, nub, partition
                                            , tails )
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set (Set, empty, member, insert)

import Curry.Base.Ident
import Curry.Base.Position hiding (first)
import Curry.Syntax

import Base.Expr
import Base.CurryTypes
import Base.Messages (internalError)
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Typing
import Base.Utils (fst3)

import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTypeInfo)
import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

-- The desugaring phase keeps only the type, function, and value
-- declarations of the module, i.e., type signatures are discarded.
-- While record declarations are transformed into ordinary data/newtype
-- declarations, the remaining type declarations are not desugared.
-- Since they cannot occur in local declaration groups, they are filtered
-- out separately. Actually, the transformation is slightly more general than
-- necessary as it allows value declarations at the top-level of a module.

desugar :: [KnownExtension] -> ValueEnv -> TCEnv -> Module PredType
        -> (Module PredType, ValueEnv)
desugar xs vEnv tcEnv (Module ps m es is ds)
  = (Module ps m es is ds', valueEnv s')
  where (ds', s') = S.runState (desugarModuleDecls ds)
                               (DesugarState m xs tcEnv vEnv 1)

-- ---------------------------------------------------------------------------
-- Desugaring monad and accessor functions
-- ---------------------------------------------------------------------------

-- New identifiers may be introduced while desugaring pattern declarations,
-- case and lambda-expressions, list comprehensions, and record selections
-- and updates. As usual, we use a state monad transformer for generating
-- unique names. In addition, the state is also used for passing through the
-- type environment, which must be augmented with the types of these new
-- variables.

data DesugarState = DesugarState
  { moduleIdent :: ModuleIdent      -- read-only
  , extensions  :: [KnownExtension] -- read-only
  , tyConsEnv   :: TCEnv            -- read-only
  , valueEnv    :: ValueEnv         -- will be extended
  , nextId      :: Integer          -- counter
  }

type DsM a = S.State DesugarState a

getModuleIdent :: DsM ModuleIdent
getModuleIdent = S.gets moduleIdent

checkNegativeLitsExtension :: DsM Bool
checkNegativeLitsExtension = S.gets (\s -> NegativeLiterals `elem` extensions s)

getTyConsEnv :: DsM TCEnv
getTyConsEnv = S.gets tyConsEnv

getValueEnv :: DsM ValueEnv
getValueEnv = S.gets valueEnv

getNextId :: DsM Integer
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

-- ---------------------------------------------------------------------------
-- Generation of fresh names
-- ---------------------------------------------------------------------------

-- Create a fresh variable ident for a given prefix with a monomorphic type
freshVar :: Typeable t => String -> t -> DsM (PredType, Ident)
freshVar prefix t = do
  v <- (mkIdent . (prefix ++) . show) <$> getNextId
  return (predType $ typeOf t, v)

-- ---------------------------------------------------------------------------
-- Desugaring
-- ---------------------------------------------------------------------------

desugarModuleDecls :: [Decl PredType] -> DsM [Decl PredType]
desugarModuleDecls ds = do
  ds'   <- concatMapM dsRecordDecl ds -- convert record decls to data decls
  ds''  <- mapM dsClassAndInstanceDecl ds'
  ds''' <- dsDeclGroup ds''
  return $ filter (not . liftM2 (||) isValueDecl isTypeSig) ds'' ++ ds'''

-- -----------------------------------------------------------------------------
-- Desugaring of class and instance declarations
-- -----------------------------------------------------------------------------

dsClassAndInstanceDecl :: Decl PredType -> DsM (Decl PredType)
dsClassAndInstanceDecl (ClassDecl p cx cls tv ds) =
  ClassDecl p cx cls tv . (tds ++) <$> dsDeclGroup vds
  where (tds, vds) = partition isTypeSig ds
dsClassAndInstanceDecl (InstanceDecl p cx cls ty ds) =
  InstanceDecl p cx cls ty <$> dsDeclGroup ds
dsClassAndInstanceDecl d = return d

-- -----------------------------------------------------------------------------
-- Desugaring of type declarations: records
-- -----------------------------------------------------------------------------

-- As an extension to the Curry language, the compiler supports Haskell's
-- record syntax, which introduces field labels for data and renaming types.
-- Field labels can be used in constructor declarations, patterns,
-- and expressions. For further convenience, an implicit selector
-- function is introduced for each field label.

-- Generate selector functions for record labels and replace record
-- constructor declarations by ordinary constructor declarations.
dsRecordDecl :: Decl PredType -> DsM [Decl PredType]
dsRecordDecl (DataDecl p tc tvs cs clss) = do
  m <- getModuleIdent
  let qcs = map (qualifyWith m . constrId) cs
  selFuns <- mapM (genSelFun p qcs) (nub $ concatMap recordLabels cs)
  return $ DataDecl p tc tvs (map unlabelConstr cs) clss : selFuns
dsRecordDecl (NewtypeDecl p tc tvs nc clss) = do
  m <- getModuleIdent
  let qc = qualifyWith m (nconstrId nc)
  selFun <- mapM (genSelFun p [qc]) (nrecordLabels nc)
  return $ NewtypeDecl p tc tvs (unlabelNewConstr nc) clss : selFun
dsRecordDecl d = return [d]

-- Generate a selector function for a single record label
genSelFun :: Position -> [QualIdent] -> Ident -> DsM (Decl PredType)
genSelFun p qcs l = do
  m <- getModuleIdent
  vEnv <- getValueEnv
  let ForAll _ pty = varType (qualifyWith m l) vEnv
  FunctionDecl p pty l <$> concatMapM (genSelEqn p l) qcs

-- Generate a selector equation for a label and a constructor if the label
-- is applicable, otherwise the empty list is returned.
genSelEqn :: Position -> Ident -> QualIdent -> DsM [Equation PredType]
genSelEqn p l qc = do
  vEnv <- getValueEnv
  let (ls, ty) = conType qc vEnv
      (tys, ty0) = arrowUnapply (instType ty)
  case elemIndex l ls of
    Just n  -> do
      vs <- mapM (freshVar "_#rec") tys
      let pat = constrPattern (predType ty0) qc vs
      return [mkEquation p l [pat] (uncurry mkVar (vs !! n))]
    Nothing -> return []

-- Remove any labels from a data constructor declaration
unlabelConstr :: ConstrDecl -> ConstrDecl
unlabelConstr (RecordDecl p evs cx c fs) = ConstrDecl p evs cx c tys
  where tys = [ty | FieldDecl _ ls ty <- fs, _ <- ls]
unlabelConstr c                          = c

-- Remove any labels from a newtype constructor declaration
unlabelNewConstr :: NewConstrDecl -> NewConstrDecl
unlabelNewConstr (NewRecordDecl p nc (_, ty)) = NewConstrDecl p nc ty
unlabelNewConstr c                            = c

-- -----------------------------------------------------------------------------
-- Desugaring of value declarations
-- -----------------------------------------------------------------------------

-- Within a declaration group, all type signatures are discarded. First,
-- the patterns occurring in the left hand sides of pattern declarations
-- and external declarations are desugared. Due to lazy patterns, the former
-- may add further declarations to the group that must be desugared as well.
dsDeclGroup :: [Decl PredType] -> DsM [Decl PredType]
dsDeclGroup ds = concatMapM dsDeclLhs (filter isValueDecl ds) >>= mapM dsDeclRhs

dsDeclLhs :: Decl PredType -> DsM [Decl PredType]
dsDeclLhs (PatternDecl p t rhs) = do
  (ds', t') <- dsPat p [] t
  dss'      <- mapM dsDeclLhs ds'
  return $ PatternDecl p t' rhs : concat dss'
dsDeclLhs (ExternalDecl   p vs) = return $ map (genForeignDecl p) vs
dsDeclLhs d                     = return [d]

genForeignDecl :: Position -> Var PredType -> Decl PredType
genForeignDecl p (Var pty v) =
  ForeignDecl p CallConvPrimitive (Just $ idName v) pty v $
    fromType identSupply $ typeOf pty

-- TODO: Check if obsolete and remove
-- After desugaring its right hand side, each equation is eta-expanded
-- by adding as many variables as necessary to the argument list and
-- applying the right hand side to those variables (Note: eta-expansion
-- is disabled in the version for PAKCS).
-- Furthermore every occurrence of a record type within the type of a function
-- is simplified to the corresponding type constructor from the record
-- declaration. This is possible because currently records must not be empty
-- and a record label belongs to only one record declaration.

-- Desugaring of the right-hand-side of declarations
dsDeclRhs :: Decl PredType -> DsM (Decl PredType)
dsDeclRhs (FunctionDecl     p pty f eqs) =
  FunctionDecl p pty f <$> mapM dsEquation eqs
dsDeclRhs (PatternDecl          p t rhs) = PatternDecl p t <$> dsRhs p id rhs
dsDeclRhs (ForeignDecl p cc ie pty f ty) =
  return $ ForeignDecl p cc ie' pty f ty
  where ie' = ie `mplus` Just (idName f)
dsDeclRhs fs@(FreeDecl              _ _) = return fs
dsDeclRhs _                              =
  error "Desugar.dsDeclRhs: no pattern match"

-- Desugaring of an equation
dsEquation :: Equation PredType -> DsM (Equation PredType)
dsEquation (Equation p lhs rhs) = do
  (     cs1, ts1) <- dsNonLinearity         ts
  (ds1, cs2, ts2) <- dsFunctionalPatterns p ts1
  (ds2,      ts3) <- mapAccumM (dsPat p) [] ts2
  rhs'            <- dsRhs p (constrain cs2 . constrain cs1)
                             (addDecls (ds1 ++ ds2) rhs)
  return $ Equation p (FunLhs f ts3) rhs'
  where (f, ts) = flatLhs lhs

-- Constrain an expression by a list of constraints.
-- @constrain []  e  ==  e@
-- @constrain c_n e  ==  (c_1 & ... & c_n) &> e@
constrain :: [Expression PredType] -> Expression PredType -> Expression PredType
constrain cs e = if null cs then e else foldr1 (&) cs &> e

-- -----------------------------------------------------------------------------
-- Desugaring of right-hand sides
-- -----------------------------------------------------------------------------

-- A list of boolean guards is expanded into a nested if-then-else
-- expression, whereas a constraint guard is replaced by a case
-- expression. Note that if the guard type is 'Success' only a
-- single guard is allowed for each equation (This change was
-- introduced in version 0.8 of the Curry report.). We check for the
-- type 'Bool' of the guard because the guard's type defaults to
-- 'Success' if it is not restricted by the guard expression.

dsRhs :: Position -> (Expression PredType -> Expression PredType)
      -> Rhs PredType -> DsM (Rhs PredType)
dsRhs p f rhs =     expandRhs (prelFailed (typeOf rhs)) f rhs
                >>= dsExpr pRhs
                >>= return . simpleRhs pRhs
  where
  pRhs = fromMaybe p (getRhsPosition rhs)

expandRhs :: Expression PredType -> (Expression PredType -> Expression PredType)
          -> Rhs PredType -> DsM (Expression PredType)
expandRhs _  f (SimpleRhs _ e ds) = return $ Let ds (f e)
expandRhs e0 f (GuardedRhs es ds) = (Let ds . f) <$> expandGuards e0 es

expandGuards :: Expression PredType -> [CondExpr PredType]
             -> DsM (Expression PredType)
expandGuards e0 es =
  return $ if boolGuards es then foldr mkIfThenElse e0 es else mkCond es
  where
  mkIfThenElse (CondExpr p g e) = IfThenElse (srcRefOf p) g e
  mkCond [CondExpr _ g e] = g &> e
  mkCond _                = error "Desugar.expandGuards.mkCond: non-unary list"

boolGuards :: [CondExpr PredType] -> Bool
boolGuards []                    = False
boolGuards (CondExpr _ g _ : es) = not (null es) || typeOf g == boolType

-- Add additional declarations to a right-hand side
addDecls :: [Decl PredType] -> Rhs PredType -> Rhs PredType
addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

getRhsPosition :: Rhs a -> Maybe Position
getRhsPosition (SimpleRhs p _ _) = Just p
getRhsPosition (GuardedRhs  _ _) = Nothing

-- -----------------------------------------------------------------------------
-- Desugaring of non-linear patterns
-- -----------------------------------------------------------------------------

-- The desugaring traverses a pattern in depth-first order and collects
-- all variables. If it encounters a variable which has been previously
-- introduced, the second occurrence is changed to a fresh variable
-- and a new pair (newvar, oldvar) is saved to generate constraints later.
-- Non-linear patterns inside single functional patterns are not desugared,
-- as this special case is handled later.
dsNonLinearity :: [Pattern PredType]
               -> DsM ([Expression PredType], [Pattern PredType])
dsNonLinearity ts = do
  ((_, cs), ts') <- mapAccumM dsNonLinear (Set.empty, []) ts
  return (reverse cs, ts')

type NonLinearEnv = (Set.Set Ident, [Expression PredType])

dsNonLinear :: NonLinearEnv -> Pattern PredType
            -> DsM (NonLinearEnv, Pattern PredType)
dsNonLinear env l@(LiteralPattern        _ _) = return (env, l)
dsNonLinear env n@(NegativePattern     _ _ _) = return (env, n)
dsNonLinear env t@(VariablePattern       _ v)
  | isAnonId v         = return (env, t)
  | v `Set.member` vis = do
    v' <- freshVar "_#nonlinear" t
    return ((vis, mkStrictEquality v v' : eqs), uncurry VariablePattern v')
  | otherwise          = return ((Set.insert v vis, eqs), t)
  where (vis, eqs) = env
dsNonLinear env (ConstructorPattern pty c ts) = second (ConstructorPattern pty c)
                                                <$> mapAccumM dsNonLinear env ts
dsNonLinear env (InfixPattern   pty t1 op t2) = do
  (env1, t1') <- dsNonLinear env  t1
  (env2, t2') <- dsNonLinear env1 t2
  return (env2, InfixPattern pty t1' op t2')
dsNonLinear env (ParenPattern            t) = second ParenPattern
                                              <$> dsNonLinear env t
dsNonLinear env (RecordPattern      pty c fs) =
  second (RecordPattern pty c) <$> mapAccumM (dsField dsNonLinear) env fs
dsNonLinear env (TuplePattern         pos ts) = second (TuplePattern pos)
                                                <$> mapAccumM dsNonLinear env ts
dsNonLinear env (ListPattern      pty pos ts) = second (ListPattern pty pos)
                                                <$> mapAccumM dsNonLinear env ts
dsNonLinear env (AsPattern             v t) = do
  let pty = predType $ typeOf t
  (env1, VariablePattern _ v') <- dsNonLinear env (VariablePattern pty v)
  (env2, t') <- dsNonLinear env1 t
  return (env2, AsPattern v' t')
dsNonLinear env (LazyPattern             r t) = second (LazyPattern r)
                                                <$> dsNonLinear env t
dsNonLinear env fp@(FunctionPattern    _ _ _) = dsNonLinearFuncPat env fp
dsNonLinear env fp@(InfixFuncPattern _ _ _ _) = dsNonLinearFuncPat env fp

dsNonLinearFuncPat :: NonLinearEnv -> Pattern PredType
                   -> DsM (NonLinearEnv, Pattern PredType)
dsNonLinearFuncPat (vis, eqs) fp = do
  let fpVars = map (\(v, _, pty) -> (pty, v)) $ patternVars fp
      vs     = filter ((`Set.member` vis) . snd) fpVars
  vs' <- mapM (freshVar "_#nonlinear" . uncurry VariablePattern) vs
  let vis' = foldr (Set.insert . snd) vis fpVars
      fp'  = substPat (zip (map snd vs) (map snd vs')) fp
  return ((vis', zipWith mkStrictEquality (map snd vs) vs' ++ eqs), fp')

mkStrictEquality :: Ident -> (PredType, Ident) -> Expression PredType
mkStrictEquality x (pty, y) = mkVar pty x =:= mkVar pty y

substPat :: [(Ident, Ident)] -> Pattern a -> Pattern a
substPat _ l@(LiteralPattern        _ _) = l
substPat _ n@(NegativePattern     _ _ _) = n
substPat s (VariablePattern         a v) = VariablePattern a
                                         $ fromMaybe v (lookup v s)
substPat s (ConstructorPattern   a c ps) = ConstructorPattern a c
                                         $ map (substPat s) ps
substPat s (InfixPattern     a p1 op p2) = InfixPattern a (substPat s p1) op
                                                        (substPat s p2)
substPat s (ParenPattern              p) = ParenPattern (substPat s p)
substPat s (RecordPattern        a c fs) = RecordPattern a c (map substField fs)
  where substField (Field pos l pat) = Field pos l (substPat s pat)
substPat s (TuplePattern         pos ps) = TuplePattern pos
                                         $ map (substPat s) ps
substPat s (ListPattern        a pos ps) = ListPattern a pos
                                         $ map (substPat s) ps
substPat s (AsPattern               v p) = AsPattern (fromMaybe v (lookup v s))
                                                     (substPat s p)
substPat s (LazyPattern             r p) = LazyPattern r (substPat s p)
substPat s (FunctionPattern      a f ps) = FunctionPattern a f
                                         $ map (substPat s) ps
substPat s (InfixFuncPattern a p1 op p2) = InfixFuncPattern a (substPat s p1) op
                                                            (substPat s p2)

-- -----------------------------------------------------------------------------
-- Desugaring of functional patterns
-- -----------------------------------------------------------------------------

-- Desugaring of functional patterns works in the following way:
--  1. The patterns are recursively traversed from left to right
--     to extract every functional pattern (note that functional patterns
--     can not be nested).
--     Each pattern is replaced by a fresh variable and a pair
--     (variable, functional pattern) is generated.
--  2. The variable-pattern pairs of the form @(v, p)@ are collected and
--     transformed into additional constraints of the form @p =:<= v@,
--     where the pattern @p@ is converted to the corresponding expression.
--     In addition, any variable occurring in @p@ is declared as a fresh
--     free variable.
--     Multiple constraints will later be combined using the @&>@-operator
--     such that the patterns are evaluated from left to right.

dsFunctionalPatterns
  :: Position -> [Pattern PredType]
  -> DsM ([Decl PredType], [Expression PredType], [Pattern PredType])
dsFunctionalPatterns p ts = do
  -- extract functional patterns
  (bs, ts') <- mapAccumM elimFP [] ts
  -- generate declarations of free variables and constraints
  let (ds, cs) = genFPExpr p (concatMap patternVars ts') (reverse bs)
  -- return (declarations, constraints, desugared patterns)
  return (ds, cs, ts')

type LazyBinding = (Pattern PredType, (PredType, Ident))

elimFP :: [LazyBinding] -> Pattern PredType
       -> DsM ([LazyBinding], Pattern PredType)
elimFP bs p@(LiteralPattern        _ _) = return (bs, p)
elimFP bs p@(NegativePattern     _ _ _) = return (bs, p)
elimFP bs p@(VariablePattern       _ _) = return (bs, p)
elimFP bs (ConstructorPattern pty c ts) = second (ConstructorPattern pty c)
                                          <$> mapAccumM elimFP bs ts
elimFP bs (InfixPattern   pty t1 op t2) = do
  (bs1, t1') <- elimFP bs  t1
  (bs2, t2') <- elimFP bs1 t2
  return (bs2, InfixPattern pty t1' op t2')
elimFP bs (ParenPattern              t) = second ParenPattern <$> elimFP bs t
elimFP bs (RecordPattern      pty c fs) = second (RecordPattern pty c)
                                          <$> mapAccumM (dsField elimFP) bs fs
elimFP bs (TuplePattern         pos ts) = second (TuplePattern pos)
                                          <$> mapAccumM elimFP bs ts
elimFP bs (ListPattern      pty pos ts) = second (ListPattern pty pos)
                                          <$> mapAccumM elimFP bs ts
elimFP bs (AsPattern               v t) = second (AsPattern   v) <$> elimFP bs t
elimFP bs (LazyPattern             r t) = second (LazyPattern r) <$> elimFP bs t
elimFP bs p@(FunctionPattern     _ _ _) = do
 (pty, v) <- freshVar "_#funpatt" p
 return ((p, (pty, v)) : bs, VariablePattern pty v)
elimFP bs p@(InfixFuncPattern  _ _ _ _) = do
 (pty, v) <- freshVar "_#funpatt" p
 return ((p, (pty, v)) : bs, VariablePattern pty v)

genFPExpr :: Position -> [(Ident, Int, PredType)] -> [LazyBinding]
          -> ([Decl PredType], [Expression PredType])
genFPExpr p vs bs
  | null bs   = ([]               , [])
  | null free = ([]               , cs)
  | otherwise = ([FreeDecl p (map (\(v, _, pty) -> Var pty v) free)], cs)
  where
  mkLB (t, (pty, v)) = let (t', es) = fp2Expr t
                       in  (t' =:<= mkVar pty v) : es
  cs   = concatMap mkLB bs
  free = nub $ filter (not . isAnonId . fst3) $
                 concatMap patternVars (map fst bs) \\ vs

fp2Expr :: Pattern PredType -> (Expression PredType, [Expression PredType])
fp2Expr (LiteralPattern          pty l) = (Literal pty l, [])
fp2Expr (NegativePattern       pty _ l) = (Literal pty (negateLiteral l), [])
fp2Expr (VariablePattern         pty v) = (mkVar pty v, [])
fp2Expr (ConstructorPattern   pty c ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (apply (Constructor pty c) ts', concat ess)
fp2Expr (InfixPattern   pty t1 op t2) =
  let (t1', es1) = fp2Expr t1
      (t2', es2) = fp2Expr t2
      pty' = predType $ TypeArrow (typeOf t1') $ TypeArrow (typeOf t2') $ unpredType pty
  in  (InfixApply t1' (InfixConstr pty' op) t2', es1 ++ es2)
fp2Expr (ParenPattern                t) = first Paren (fp2Expr t)
fp2Expr (TuplePattern             r ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (Tuple r ts', concat ess)
fp2Expr (ListPattern         pty rs ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (List pty rs ts', concat ess)
fp2Expr (FunctionPattern      pty f ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (apply (Variable pty f) ts', concat ess)
fp2Expr (InfixFuncPattern pty t1 op t2) =
  let (t1', es1) = fp2Expr t1
      (t2', es2) = fp2Expr t2
      pty' = predType $ TypeArrow (typeOf t1') $ TypeArrow (typeOf t2') $ unpredType pty
  in  (InfixApply t1' (InfixOp pty' op) t2', es1 ++ es2)
fp2Expr (AsPattern                 v t) =
  let (t', es) = fp2Expr t
      pty = predType $ typeOf t
  in  (mkVar pty v, (t' =:<= mkVar pty v) : es)
fp2Expr (RecordPattern        pty c fs) =
  let (fs', ess) = unzip [ (Field p f e, es) | Field p f t <- fs
                                             , let (e, es) = fp2Expr t]
  in  (Record pty c fs', concat ess)
fp2Expr t                               = internalError $
  "Desugar.fp2Expr: Unexpected constructor term: " ++ show t

-- -----------------------------------------------------------------------------
-- Desugaring of ordinary patterns
-- -----------------------------------------------------------------------------

-- The transformation of patterns is straight forward except for lazy
-- patterns. A lazy pattern '~t' is replaced by a fresh
-- variable 'v' and a new local declaration 't = v' in the
-- scope of the pattern. In addition, as-patterns 'v@t' where
-- 't' is a variable or an as-pattern are replaced by 't' in combination
-- with a local declaration for 'v'.

-- Record patterns are transformed into normal constructor patterns by
-- rearranging fields in the order of the record's declaration, adding
-- fresh variables in place of omitted fields, and discarding the field
-- labels.

-- Note: By rearranging fields here we loose the ability to comply
-- strictly with the Haskell 98 pattern matching semantics, which matches
-- fields of a record pattern in the order of their occurrence in the
-- pattern. However, keep in mind that Haskell matches alternatives from
-- top to bottom and arguments within an equation or alternative from
-- left to right, which is not the case in Curry except for rigid case
-- expressions.

dsLiteralPat :: PredType -> Literal
             -> Either (Pattern PredType) (Pattern PredType)
dsLiteralPat pty c@(Char _ _) = Right (LiteralPattern pty c)
dsLiteralPat pty (Int ref i) =
  Right (LiteralPattern pty (fixLiteral (unpredType pty)))
  where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
        fixLiteral ty
          | ty == floatType = Float ref $ fromInteger i
          | otherwise = Int ref i
dsLiteralPat pty f@(Float _ _) = Right (LiteralPattern pty f)
dsLiteralPat pty (String (SrcRef [i]) cs) =
  Left $ ListPattern pty (consRefs i cs) $
    map (LiteralPattern pty') $ zipWith (Char . SrcRef . (:[])) [i, i + 2 ..] cs
  where pty' = predType $ elemType $ unpredType pty
        -- TODO: Share with 'dsLiteral'
        consRefs r []     = [SrcRef [r]]
        consRefs r (_:xs) = let r' = r + 2
                            in  r' `seq` (SrcRef [r'] : consRefs r' xs)
dsLiteralPat _ (String _ _) = internalError $
  "Desugar.dsLiteralPat: wrong source ref for string"

dsPat :: Position -> [Decl PredType] -> Pattern PredType
      -> DsM ([Decl PredType], Pattern PredType)
dsPat _ ds v@(VariablePattern     _ _) = return (ds, v)
dsPat p ds (LiteralPattern      pty l) =
  either (dsPat p ds) (return . (,) ds) (dsLiteralPat pty l)
dsPat p ds (NegativePattern   pty _ l) =
  dsPat p ds (LiteralPattern pty (negateLiteral l))
dsPat p ds (ConstructorPattern pty c [t]) = do
  isNc <- isNewtypeConstr c
  if isNc then dsPat p ds t else second (constrPat c) <$> dsPat p ds t
  where constrPat c' t' = ConstructorPattern pty c' [t']
dsPat p ds (ConstructorPattern pty c ts) =
  second (ConstructorPattern pty c) <$> mapAccumM (dsPat p) ds ts
dsPat p ds (InfixPattern  pty t1 op t2) =
  dsPat p ds (ConstructorPattern pty op [t1, t2])
dsPat p ds (ParenPattern           t) = dsPat p ds t
dsPat p ds (RecordPattern   pty c fs) = do
  vEnv <- getValueEnv
  --TODO: Rework
  let (ls, tys) = argumentTypes (unpredType pty) c vEnv
      tsMap = map field2Tuple fs
      anonTs = map (flip VariablePattern anonId . predType) tys
      maybeTs = map (flip lookup tsMap) ls
      ts = zipWith fromMaybe anonTs maybeTs
  dsPat p ds (ConstructorPattern pty c ts)
dsPat p ds (TuplePattern      pos ts) =
  dsPat p ds (ConstructorPattern pty (addRef pos $ qTupleId $ length ts) ts)
  where pty = predType (tupleType (map typeOf ts))
dsPat p ds (ListPattern      pty pos ts) =
  second (dsList pos cons nil) <$> mapAccumM (dsPat p) ds ts
  where nil  p' = ConstructorPattern pty (addRef p' qNilId) []
        cons p' t ts' = ConstructorPattern pty (addRef p' qConsId) [t, ts']
dsPat p ds (AsPattern            v t) = dsAs p v <$> dsPat p ds t
dsPat p ds (LazyPattern          r t) = dsLazy r p ds t
dsPat p ds (FunctionPattern    pty f ts) = second (FunctionPattern pty f)
                                        <$> mapAccumM (dsPat p) ds ts
dsPat p ds (InfixFuncPattern pty t1 f t2) =
  dsPat p ds (FunctionPattern pty f [t1, t2])

dsAs :: Position -> Ident -> ([Decl PredType], Pattern PredType)
     -> ([Decl PredType], Pattern PredType)
dsAs p v (ds, t) = case t of
  VariablePattern pty v' -> (varDecl p pty v (mkVar pty v') : ds, t)
  AsPattern        v' t' -> (varDecl p pty' v (mkVar pty' v') : ds, t)
    where pty' = predType $ typeOf t'
  _                      -> (ds, AsPattern v t)

dsLazy :: SrcRef -> Position -> [Decl PredType] -> Pattern PredType
       -> DsM ([Decl PredType], Pattern PredType)
dsLazy pos p ds t = case t of
  VariablePattern _ _ -> return (ds, t)
  ParenPattern     t' -> dsLazy pos p ds t'
  AsPattern      v t' -> dsAs p v <$> dsLazy pos p ds t'
  LazyPattern pos' t' -> dsLazy pos' p ds t'
  _                   -> do
    (pty, v'') <- freshVar "_#lazy" t
    v' <- addPositionIdent (AST pos) <$> return v''
    return ( patDecl p { astRef = pos } t (mkVar pty v') : ds
           , VariablePattern pty v' )

{-
-- -----------------------------------------------------------------------------
-- Desugaring of expressions
-- -----------------------------------------------------------------------------

-- Record construction expressions are transformed into normal
-- constructor applications by rearranging fields in the order of the
-- record's declaration, passing `Prelude.unknown` in place of
-- omitted fields, and discarding the field labels. The transformation of
-- record update expressions is a bit more involved as we must match the
-- updated expression with all valid constructors of the expression's
-- type. As stipulated by the Haskell 98 Report, a record update
-- expression @e { l_1 = e_1, ..., l_k = e_k }@ succeeds only if @e@ reduces to
-- a value @C e'_1 ... e'_n@ such that @C@'s declaration contains all
-- field labels @l_1,...,l_k@. In contrast to Haskell, we do not report
-- an error if this is not the case, but call failed instead.
-}
dsExpr :: Position -> Expression PredType -> DsM (Expression PredType)
dsExpr p (Literal     pty l) =
  either (dsExpr p) return (dsLiteral pty l)
dsExpr _ var@(Variable pty v)
  | isAnonId (unqualify v)   = return $ prelUnknown $ unpredType pty
  | otherwise                = return var
dsExpr _ c@(Constructor _ _) = return c
dsExpr p (Paren           e) = dsExpr p e
dsExpr p (Typed       e qty) = Typed <$> dsExpr p e <*> dsQualTypeExpr qty
dsExpr p (Record   pty c fs) = do
  vEnv <- getValueEnv
  --TODO: Rework
  let (ls, tys) = argumentTypes (unpredType pty) c vEnv
      esMap = map field2Tuple fs
      unknownEs = map prelUnknown tys
      maybeEs = map (flip lookup esMap) ls
      es = zipWith fromMaybe unknownEs maybeEs
  dsExpr p (applyConstr pty c tys es)
dsExpr p (RecordUpdate e fs) = do
  alts  <- constructors tc >>= concatMapM updateAlt
  dsExpr p $ Case (srcRefOf p) Flex e (map (uncurry (caseAlt p)) alts)
  where ty = typeOf e
        pty = predType ty
        TypeConstructor tc = arrowBase ty
        updateAlt (RecordConstr c _ _ ls tys)
          | all (`elem` qls) (map fieldLabel fs)= do
            vs <- mapM (freshVar "_#rec") tys
            let qc = qualifyLike tc c
                pat = constrPattern pty qc vs
                esMap = map field2Tuple fs
                originalEs = map (uncurry mkVar) vs
                maybeEs = map (flip lookup esMap) qls
                es = zipWith fromMaybe originalEs maybeEs
            return [(pat, applyConstr pty qc tys es)]
          where qls = map (qualifyLike tc) ls
        updateAlt _ = return []
dsExpr p (Tuple      ref es) = apply (Constructor pty $ addRef ref $ qTupleId $ length es) <$> mapM (dsExpr p) es
  where pty = predType (foldr TypeArrow (tupleType tys) tys)
        tys = map typeOf es
dsExpr p (List   pty refs es) = dsList refs cons nil <$> mapM (dsExpr p) es
  where nil  p' = Constructor pty (addRef p' qNilId)
        cons p' = Apply . Apply (Constructor (predType $ consType $ elemType $ unpredType pty) (addRef p' qConsId))
dsExpr p (ListCompr        r e qs) = dsListComp p r e qs
dsExpr p (EnumFrom              e) = Apply (prelEnumFrom (typeOf e))
                                     <$> dsExpr p e
dsExpr p (EnumFromThen      e1 e2) = apply (prelEnumFromThen (typeOf e1))
                                     <$> mapM (dsExpr p) [e1, e2]
dsExpr p (EnumFromTo        e1 e2) = apply (prelEnumFromTo (typeOf e1))
                                     <$> mapM (dsExpr p) [e1, e2]
dsExpr p (EnumFromThenTo e1 e2 e3) = apply (prelEnumFromThenTo (typeOf e1))
                                     <$> mapM (dsExpr p) [e1, e2, e3]
dsExpr p (UnaryMinus          _ e) = do
  e' <- dsExpr p e
  negativeLitsEnabled <- checkNegativeLitsExtension
  return $ case e' of
    Literal pty l | negativeLitsEnabled -> Literal pty $ negateLiteral l
    _                                   -> Apply (prelNegate $ typeOf e') e'
dsExpr p (Apply (Constructor pty c) e) = do
  isNc <- isNewtypeConstr c
  if isNc then dsExpr p e else Apply (Constructor pty c) <$> dsExpr p e
dsExpr p (Apply e1 e2) = Apply <$> dsExpr p e1 <*> dsExpr p e2
dsExpr p (InfixApply e1 op e2) = do
  op' <- dsExpr p (infixOp op)
  e1' <- dsExpr p e1
  e2' <- dsExpr p e2
  return $ apply op' [e1', e2']
dsExpr p (LeftSection  e op) = Apply <$> dsExpr p (infixOp op) <*> dsExpr p e
dsExpr p (RightSection op e) = do
  op' <- dsExpr p (infixOp op)
  e'  <- dsExpr p e
  return $ apply (prelFlip ty1 ty2 ty3) [op', e']
  where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
dsExpr p expr@(Lambda r ts e) = do
  (pty, f) <- freshVar "_#lambda" expr
  dsExpr p $ Let [funDecl (AST r) pty f ts e] $ mkVar pty f
dsExpr p (Let ds e) = do
  ds' <- dsDeclGroup ds
  e'  <- dsExpr p e
  return (if null ds' then e' else Let ds' e')
dsExpr p (Do              sts e) = dsExpr p (dsDo sts e)
dsExpr p (IfThenElse r e1 e2 e3) = do
  e1' <- dsExpr p e1
  e2' <- dsExpr p e2
  e3' <- dsExpr p e3
  return $ Case r Rigid e1' [caseAlt p truePat e2', caseAlt p falsePat e3']
dsExpr p (Case r ct e alts) = dsCase p r ct e alts

-- We ignore the context in the type signature of a typed expression, since
-- there should be no possibility to provide an non-empty context without
-- scoped type-variables.
-- TODO: Verify

dsQualTypeExpr :: QualTypeExpr -> DsM QualTypeExpr
dsQualTypeExpr (QualTypeExpr cx ty) = QualTypeExpr cx <$> dsTypeExpr ty

dsTypeExpr :: TypeExpr -> DsM TypeExpr
dsTypeExpr ty = do
  m <- getModuleIdent
  tcEnv <- getTyConsEnv
  return $ fromType (typeVariables ty) (expandType m tcEnv (toType [] ty))

-- -----------------------------------------------------------------------------
-- Desugaring of case expressions
-- -----------------------------------------------------------------------------

-- If an alternative in a case expression has boolean guards and all of
-- these guards return 'False', the enclosing case expression does
-- not fail but continues to match the remaining alternatives against the
-- selector expression. In order to implement this semantics, which is
-- compatible with Haskell, we expand an alternative with boolean guards
-- such that it evaluates a case expression with the remaining cases that
-- are compatible with the matched pattern when the guards fail.

dsCase :: Position -> SrcRef -> CaseType -> Expression PredType
       -> [Alt PredType] -> DsM (Expression PredType)
dsCase p r ct e alts
  | null alts = internalError "Desugar.dsCase: empty list of alternatives"
  | otherwise = do
    m  <- getModuleIdent
    e' <- dsExpr p e
    v  <- freshVar "_#case" e
    alts'  <- mapM dsAltLhs alts
    alts'' <- mapM (expandAlt v ct) (init (tails alts')) >>= mapM dsAltRhs
    return (mkCase m v e' alts'')
  where
  mkCase m (pty, v) e' bs
    | v `elem` qfv m bs = Let [varDecl p pty v e'] (Case r ct (mkVar pty v) bs)
    | otherwise         = Case r ct e' bs

dsAltLhs :: Alt PredType -> DsM (Alt PredType)
dsAltLhs (Alt p t rhs) = do
  (ds', t') <- dsPat p [] t
  return $ Alt p t' (addDecls ds' rhs)

dsAltRhs :: Alt PredType -> DsM (Alt PredType)
dsAltRhs (Alt p t rhs) = Alt p t <$> dsRhs p id rhs

expandAlt :: (PredType, Ident) -> CaseType -> [Alt PredType]
          -> DsM (Alt PredType)
expandAlt _ _  []                   = error "Desugar.expandAlt: empty list"
expandAlt v ct (Alt p t rhs : alts) = caseAlt p t <$> expandRhs e0 id rhs
  where
  e0 | ct == Flex || null compAlts = prelFailed (typeOf rhs)
     | otherwise = Case (srcRefOf p) ct (uncurry mkVar v) compAlts
  compAlts = filter (isCompatible t . altPattern) alts
  altPattern (Alt _ t1 _) = t1

isCompatible :: Pattern a -> Pattern a -> Bool
isCompatible (VariablePattern _ _) _ = True
isCompatible _ (VariablePattern _ _) = True
isCompatible (AsPattern _ t1) t2 = isCompatible t1 t2
isCompatible t1 (AsPattern _ t2) = isCompatible t1 t2
isCompatible (ConstructorPattern _ c1 ts1) (ConstructorPattern _ c2 ts2)
  = and ((c1 == c2) : zipWith isCompatible ts1 ts2)
isCompatible (LiteralPattern _ l1) (LiteralPattern _ l2) = l1 == l2
isCompatible _ _ = False

-- -----------------------------------------------------------------------------
-- Desugaring of do-Notation
-- -----------------------------------------------------------------------------

-- The do-notation is desugared in the following way:
--
-- `dsDo([]         , e)` -> `e`
-- `dsDo(e'     ; ss, e)` -> `e' >>        dsDo(ss, e)`
-- `dsDo(p <- e'; ss, e)` -> `e' >>= \p -> dsDo(ss, e)`
-- `dsDo(let ds ; ss, e)` -> `let ds in    dsDo(ss, e)`
dsDo :: [Statement PredType] -> Expression PredType -> Expression PredType
dsDo sts e = foldr dsStmt e sts

dsStmt :: Statement PredType -> Expression PredType -> Expression PredType
dsStmt (StmtExpr r   e1) e' =
  apply (prelBind_ (typeOf e1) (typeOf e') r) [e1, e']
dsStmt (StmtBind r t e1) e' =
  apply (prelBind (typeOf e1) (typeOf t) (typeOf e') r) [e1, Lambda r [t] e']
dsStmt (StmtDecl     ds) e' = Let ds e'

-- -----------------------------------------------------------------------------
-- Desugaring of List Comprehensions
-- -----------------------------------------------------------------------------

-- In general, a list comprehension of the form
-- '[e | t <- l, qs]'
-- is transformed into an expression 'foldr f [] l' where 'f'
-- is a new function defined as
--
--     f x xs =
--       case x of
--           t -> [e | qs] ++ xs
--           _ -> xs
--
-- Note that this translation evaluates the elements of 'l' rigidly,
-- whereas the translation given in the Curry report is flexible.
-- However, it does not seem very useful to have the comprehension
-- generate instances of 't' which do not contribute to the list.
-- TODO: Unfortunately, this is incorrect.

-- Actually, we generate slightly better code in a few special cases.
-- When 't' is a plain variable, the 'case' expression degenerates
-- into a let-binding and the auxiliary function thus becomes an alias
-- for '(++)'. Instead of 'foldr (++)' we use the
-- equivalent prelude function 'concatMap'. In addition, if the
-- remaining list comprehension in the body of the auxiliary function has
-- no qualifiers -- i.e., if it is equivalent to '[e]' -- we
-- avoid the construction of the singleton list by calling '(:)'
-- instead of '(++)' and 'map' in place of 'concatMap', respectively.

dsListComp :: Position -> SrcRef -> Expression PredType -> [Statement PredType]
           -> DsM (Expression PredType)
dsListComp p r e []     =
  dsExpr p (List (predType $ listType $ typeOf e) [r,r] [e])
dsListComp p r e (q:qs) = dsQual p q (ListCompr r e qs)

dsQual :: Position -> Statement PredType -> Expression PredType
       -> DsM (Expression PredType)
dsQual p (StmtExpr   r b) e =
  dsExpr p (IfThenElse r b e (List (predType $ typeOf e) [r] []))
dsQual p (StmtDecl    ds) e = dsExpr p (Let ds e)
dsQual p (StmtBind r t l) e
  | isVariablePattern t = dsExpr p (qualExpr t e l)
  | otherwise = do
    v <- freshVar "_#var" t
    l' <- freshVar "_#var" e
    --TODO: Add SrcRefs (old version below)
    --v   <- addRefId r <$> freshVar "_#var" t
    --l'  <- addRefId r <$> freshVar "_#var" e
    dsExpr p (apply (prelFoldr (typeOf t) (typeOf e) r)
      [foldFunct v l' e, List (predType $ typeOf e) [r] [], l])
  where
  qualExpr v (ListCompr _ e1 []) l1
    = apply (prelMap (typeOf v) (typeOf e1) r) [Lambda r [v] e1, l1]
  qualExpr v e1                  l1
    = apply (prelConcatMap (typeOf v) (elemType $ typeOf e1) r) [Lambda r [v] e1, l1]
  foldFunct v l1 e1
    = Lambda r (map (uncurry VariablePattern) [v, l1])
       (Case r Rigid (uncurry mkVar v)
          [ caseAlt p t (append e1 (uncurry mkVar l1))
          , caseAlt p (uncurry VariablePattern v) (uncurry mkVar l1)])

  append (ListCompr _ e1 []) l1 = apply (prelCons (typeOf e1)) [e1, l1]
  append e1                  l1 = apply (prelAppend (elemType $ typeOf e1) r) [e1, l1]
  prelCons ty                   = Constructor (predType $ consType ty) $ addRef r $ qConsId

-- -----------------------------------------------------------------------------
-- Desugaring of Lists, labels, fields, and literals
-- -----------------------------------------------------------------------------

dsList :: [SrcRef] -> (SrcRef -> b -> b -> b) -> (SrcRef -> b) -> [b] -> b
--TODO: Fix SrcRefs here (old version below)
dsList pos cons nil xs = foldr cons' nil' xs
  where rNil : _   = reverse pos
        nil'       = nil rNil
        cons' t ts = cons rNil t ts
{-dsList pos cons nil xs = snd (foldr cons' nil' xs)
  where rNil : rCs = reverse pos
        nil'                 = (rCs , nil rNil)
        cons' t (rC:rCs',ts) = (rCs', cons rC t ts)
        cons' _ ([],_) = error "Desugar.dsList.cons': empty list"-}

--dsLabel :: a -> [(QualIdent, a)] -> QualIdent -> a
--dsLabel def fs l = fromMaybe def (lookup l fs)

dsField :: (a -> b -> DsM (a, b)) -> a -> Field b -> DsM (a, Field b)
dsField ds z (Field p l x) = second (Field p l) <$> (ds z x)

dsLiteral :: PredType -> Literal
          -> Either (Expression PredType) (Expression PredType)
dsLiteral pty (Char ref c) = Right $ Literal pty $ Char ref c
dsLiteral pty (Int ref i) = Right $ fixLiteral (unpredType pty)
  where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
        fixLiteral ty
          | ty == intType = Literal pty $ Int ref i
          | ty == floatType = Literal pty $ Float ref $ fromInteger i
          | otherwise = Apply (prelFromInteger $ unpredType pty) $
                          Literal predIntType $ Int ref i
dsLiteral pty f@(Float _ _) = Right $ fixLiteral (unpredType pty)
  where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
        fixLiteral ty
          | ty == floatType = Literal pty f
          | otherwise = Apply (prelFromRational $ unpredType pty) $
                          Literal predFloatType f
dsLiteral pty (String (SrcRef [i]) cs) =
  Left $ List pty (consRefs i cs) $
    map (Literal pty') $ zipWith (Char . SrcRef . (:[])) [i, i + 2 ..] cs
  where pty' = predType $ elemType $ unpredType pty
        -- TODO: Share with 'dsLiteralPat'
        consRefs r []     = [SrcRef [r]]
        consRefs r (_:xs) = let r' = r + 2
                            in  r' `seq` (SrcRef [r'] : consRefs r' xs)
dsLiteral _ (String _ _) = internalError $
  "Desugar.dsLiteral: wrong source ref for string"

negateLiteral :: Literal -> Literal
negateLiteral (Int ref i) = Int ref (-i)
negateLiteral (Float ref f) = Float ref (-f)
negateLiteral _ = internalError "Desugar.negateLiteral"

-- ---------------------------------------------------------------------------
-- Prelude entities
-- ---------------------------------------------------------------------------

prel :: [Type] -> Type -> String -> SrcRef -> Expression PredType
prel tys ty s r =
  Variable (predType $ foldr TypeArrow ty tys) $ addRef r $ preludeIdent s

preludeFun :: [Type] -> Type -> String -> Expression PredType
preludeFun tys ty = Variable (predType $ foldr TypeArrow ty tys) . preludeIdent

preludeIdent :: String -> QualIdent
preludeIdent = qualifyWith preludeMIdent . mkIdent

prelBind :: Type -> Type -> Type -> SrcRef -> Expression PredType
prelBind ma a mb = prel [ma, TypeArrow a mb] mb ">>="

prelBind_ :: Type -> Type -> SrcRef -> Expression PredType
prelBind_ ma mb = prel [ma, mb] mb ">>"

prelFlip :: Type -> Type -> Type -> Expression PredType
prelFlip a b c = preludeFun [TypeArrow a (TypeArrow b c), b, a] c "flip"

prelFromInteger :: Type -> Expression PredType
prelFromInteger a = preludeFun [intType] a "fromInteger"

prelFromRational :: Type -> Expression PredType
prelFromRational a = preludeFun [floatType] a "fromRational"

prelEnumFrom :: Type -> Expression PredType
prelEnumFrom a = preludeFun [a] (listType a) "enumFrom"

prelEnumFromTo :: Type -> Expression PredType
prelEnumFromTo a = preludeFun [a, a] (listType a) "enumFromTo"

prelEnumFromThen :: Type -> Expression PredType
prelEnumFromThen a = preludeFun [a, a] (listType a) "enumFromThen"

prelEnumFromThenTo :: Type -> Expression PredType
prelEnumFromThenTo a = preludeFun [a, a, a] (listType a) "enumFromThenTo"

prelNegate :: Type -> Expression PredType
prelNegate a = preludeFun [a] a "negate"

prelFailed :: Type -> Expression PredType
prelFailed a = preludeFun [] a "failed"

prelUnknown :: Type -> Expression PredType
prelUnknown a = preludeFun [] a "unknown"

prelMap :: Type -> Type -> SrcRef -> Expression PredType
prelMap a b = prel [TypeArrow a b, listType a] (listType b) "map"

prelFoldr :: Type -> Type -> SrcRef -> Expression PredType
prelFoldr a b = prel [TypeArrow a (TypeArrow b b), b, listType a] b "foldr"

prelAppend :: Type -> SrcRef -> Expression PredType
prelAppend a = prel [listType a, listType a] (listType a) "++"

prelConcatMap :: Type -> Type -> SrcRef -> Expression PredType
prelConcatMap a b =
  prel [TypeArrow a (listType b), listType a] (listType b) "concatMap"

(=:<=) :: Expression PredType -> Expression PredType -> Expression PredType
e1 =:<= e2 = apply (preludeFun [typeOf e1, typeOf e2] boolType "=:<=") [e1, e2]

(=:=) :: Expression PredType -> Expression PredType -> Expression PredType
e1 =:= e2 = apply (preludeFun [typeOf e1, typeOf e2] boolType "=:=") [e1, e2]

(&>) :: Expression PredType -> Expression PredType -> Expression PredType
e1 &> e2 = apply (preludeFun [boolType, typeOf e2] (typeOf e2) "cond") [e1, e2]

(&) :: Expression PredType -> Expression PredType -> Expression PredType
e1 & e2 = apply (preludeFun [boolType, boolType] boolType "&") [e1, e2]

truePat :: Pattern PredType
truePat = ConstructorPattern predBoolType qTrueId []

falsePat :: Pattern PredType
falsePat = ConstructorPattern predBoolType qFalseId []

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

isNewtypeConstr :: QualIdent -> DsM Bool
isNewtypeConstr c = getValueEnv >>= \vEnv -> return $
  case qualLookupValue c vEnv of
    [NewtypeConstructor _ _ _] -> True
    [DataConstructor  _ _ _ _] -> False
    x -> internalError $ "Desugar.isNewtypeConstr: " ++ show c ++ " is " ++ show x

conType :: QualIdent -> ValueEnv -> ([Ident], ExistTypeScheme)
conType c vEnv = case qualLookupValue c vEnv of
  [DataConstructor _ _ ls ty] -> (ls , ty)
  [NewtypeConstructor _ l ty] -> ([l], ty)
  _                           -> internalError $ "Desguar.conType: " ++ show c

varType :: QualIdent -> ValueEnv -> TypeScheme
varType v vEnv = case qualLookupValue v vEnv of
  Value _ _ _ tySc : _ -> tySc
  Label _ _   tySc : _ -> tySc
  _                    -> internalError $ "Desugar.varType: " ++ show v

elemType :: Type -> Type
elemType (TypeApply (TypeConstructor tc) ty) | tc == qListId = ty
elemType ty = internalError $ "Base.Types.elemType " ++ show ty

applyConstr :: PredType -> QualIdent -> [Type] -> [Expression PredType]
            -> Expression PredType
applyConstr pty c tys =
  apply (Constructor (predType (foldr TypeArrow (unpredType pty) tys)) c)

-- The function 'instType' instantiates the universally quantified
-- type variables of a type scheme with fresh type variables. Since this
-- function is used only to instantiate the closed types of record
-- constructors (recall that no existentially quantified type
-- variables are allowed for records), the compiler can reuse the same
-- monomorphic type variables for every instantiated type.

instType :: ExistTypeScheme -> Type
instType (ForAllExist _ _ pty) = inst $ unpredType pty
  where inst (TypeConstructor     tc) = TypeConstructor tc
        inst (TypeApply      ty1 ty2) = TypeApply (inst ty1) (inst ty2)
        inst (TypeVariable        tv) = TypeVariable (-1 - tv)
        inst (TypeArrow      ty1 ty2) = TypeArrow (inst ty1) (inst ty2)
        inst ty                       = ty

-- Retrieve all constructors of a type
constructors :: QualIdent -> DsM [DataConstr]
constructors tc = getTyConsEnv >>= \tcEnv -> return $
  case qualLookupTypeInfo tc tcEnv of
    [DataType     _ _ cs] -> cs
    [RenamingType _ _ nc] -> [nc]
    _                     ->
      internalError $ "Transformations.Desugar.constructors: " ++ show tc

-- The function 'argumentTypes' returns the labels and the argument types
-- of a data constructor instantiated at a particular type.

argumentTypes :: Type -> QualIdent -> ValueEnv -> ([QualIdent], [Type])
argumentTypes ty c vEnv =
  (map (qualifyLike c) ls, map (subst (matchType ty0 ty idSubst)) tys)
  where (ls, ForAllExist _ _ (PredType _ ty')) = conType c vEnv
        (tys, ty0) = arrowUnapply ty'
