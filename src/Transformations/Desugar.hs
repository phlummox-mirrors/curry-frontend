{- |
  Module      :  $Header$
  Description :  Desugaring Curry Expressions
  Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                                 Martin Engelke
                     2011 - 2015 Björn Peemöller
                     2015        Jan Tikovsky
  License     :  OtherLicense

  Maintainer  :  bjp@informatik.uni-kiel.de
  Stability   :  experimental
  Portability :  portable

  The desugaring pass removes all syntactic sugar from the module. In
  particular, the output of the desugarer will have the following
  properties.

  * No guarded right hand sides occur in equations, pattern
    declarations, and case alternatives. In addition, the declaration
    lists of the right hand sides are empty; local declarations are
    transformed into let expressions.

  * Patterns in equations and case alternatives are composed only of
    - literals,
    - variables,
    - constructor applications, and
    - as patterns.

  * Expressions are composed only of
    - literals,
    - variables,
    - constructors,
    - (binary) applications,
    - let expressions, and
    - case expressions.

  * Applications 'N x' in patterns and expressions, where 'N' is a
    newtype constructor, are replaced by a 'x'. Note that neither the
    newtype declaration itself nor partial applications of newtype
    constructors are changed.
    It were possible to replace partial applications of newtype constructor
    by 'Prelude.id'.
    However, our solution yields a more accurate output when the result
    of a computation includes partial applications.

  * Functional patterns are replaced by variables and are integrated
    in a guarded right hand side using the (=:<=) operator

  * Records, which currently must be declared using the keyword 'type',
    are transformed into data types with one constructor.
    Record construction and pattern matching are represented using the
    record constructor. Selection and update are represented using selector
    and update functions which are generated for each record declaration.
    The record constructor must be entered into the type environment as well
    as the selector functions and the update functions.

  As we are going to insert references to real prelude entities,
  all names must be properly qualified before calling this module.
-}
{-# LANGUAGE CPP #-}
module Transformations.Desugar (desugar) where

#if __GLASGOW_HASKELL__ >= 710
import           Control.Applicative        ((<$>))
#else
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Arrow              (first, second)
import           Control.Monad              (mplus)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List                  ((\\), elemIndex, nub, tails)
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set (Set, empty, member, insert)

import Curry.Base.Ident
import Curry.Base.Position hiding (first)
import Curry.Syntax

import Base.Expr
import Base.CurryTypes (toType, fromType)
import Base.Messages   (internalError)
import Base.Types
import Base.TypeSubst  (expandAliasType)
import Base.Typing
import Base.Utils      (mapAccumM, concatMapM)

import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value (ValueEnv, ValueInfo (..), bindFun, lookupValue
                 , qualLookupValue, conType)

-- New identifiers may be introduced while desugaring pattern
-- declarations, case and lambda-expressions, and list comprehensions.
-- As usual, we use a state monad transformer for generating unique
-- names. In addition, the state is also used for passing through the
-- type environment, which must be augmented with the types of these new
-- variables.

data DesugarState = DesugarState
  { moduleIdent :: ModuleIdent      -- read-only
  , extensions  :: [KnownExtension] -- read-only
  , tyConsEnv   :: TCEnv            -- read-only
  , valueEnv    :: ValueEnv
  , nextId      :: Integer     -- counter
  , desugarFP   :: Bool
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

modifyValueEnv :: (ValueEnv -> ValueEnv) -> DsM ()
modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

desugarFunPats :: DsM Bool
desugarFunPats = S.gets desugarFP

getNextId :: DsM Integer
getNextId = do
  nid <- S.gets nextId
  S.modify $ \ s -> s { nextId = succ nid }
  return nid

-- ---------------------------------------------------------------------------
-- Generation of fresh names
-- ---------------------------------------------------------------------------

getTypeOf :: Typeable t => t -> DsM Type
getTypeOf t = do
  tyEnv <- getValueEnv
  return (typeOf tyEnv t)

freshIdent :: String -> Int -> TypeScheme -> DsM Ident
freshIdent prefix arity ty = do
  m <- getModuleIdent
  x <- freeIdent
  modifyValueEnv $ bindFun m x arity ty
  return x
  where
  mkName pre n = mkIdent $ pre ++ show n
  -- TODO: This loop is only necessary because a combination of desugaring,
  -- simplification and a repeated desugaring, as currently needed for
  -- non-linear and functional patterns, may reintroduce identifiers removed
  -- during desugaring. The better solution would be to move the translation
  -- of non-linear and functional pattern into a separate module.
  freeIdent = do
    x <- mkName prefix <$> getNextId
    tyEnv <- getValueEnv
    case lookupValue x tyEnv of
      [] -> return x
      _  -> freeIdent

freshMonoTypeVar :: Typeable t => String -> t -> DsM Ident
freshMonoTypeVar prefix t = getTypeOf t >>= \ ty ->
  freshIdent prefix (arrowArity ty) (monoType ty)

-- The desugaring phase keeps only the type, function, and value
-- declarations of the module. In the current version, record declarations
-- are transformed into data types. The remaining type declarations are
-- not desugared and cannot occur in local declaration groups.
-- They are filtered out separately.

-- In order to use records within other modules, the export specification
-- of the module has to be extended with the selector and update functions of
-- all exported labels.

-- Actually, the transformation is slightly more general than necessary
-- as it allows value declarations at the top-level of a module.

desugar :: Bool -> [KnownExtension] -> ValueEnv -> TCEnv -> Module
        -> (Module, ValueEnv)
desugar dsFunPats xs tyEnv tcEnv (Module ps m es is ds)
  = (Module ps m es is ds', valueEnv s')
  where (ds', s') = S.runState (desugarModuleDecls ds)
                               (DesugarState m xs tcEnv tyEnv 1 dsFunPats)

desugarModuleDecls :: [Decl] -> DsM [Decl]
desugarModuleDecls ds = do
  ds'  <- concatMapM dsRecordDecl ds -- convert record decls to data decls
  ds'' <- dsDeclGroup ds'
  return $ filter isTypeDecl ds' ++ ds''

-- Within a declaration group, all type signatures and evaluation
-- annotations are discarded. First, the patterns occurring in the left
-- hand sides are desugared. Due to lazy patterns, this may add further
-- declarations to the group that must be desugared as well.

dsDeclGroup :: [Decl] -> DsM [Decl]
dsDeclGroup ds = concatMapM dsDeclLhs valDecls >>= mapM dsDeclRhs
 where valDecls = filter isValueDecl ds

dsDeclLhs :: Decl -> DsM [Decl]
dsDeclLhs (PatternDecl p t rhs) = do
  (ds', t') <- dsPattern p [] t
  dss'      <- mapM dsDeclLhs ds'
  return $ PatternDecl p t' rhs : concat dss'
dsDeclLhs (ExternalDecl   p fs) = mapM (genForeignDecl p) fs
dsDeclLhs d                     = return [d]

genForeignDecl :: Position -> Ident -> DsM Decl
genForeignDecl p f = do
  m     <- getModuleIdent
  ty    <- fromType <$> (getTypeOf $ Variable $ qual m f)
  return $ ForeignDecl p CallConvPrimitive (Just $ idName f) f ty
  where qual m f'
         | hasGlobalScope f' = qualifyWith m f'
         | otherwise         = qualify f'

-- After desugaring its right hand side, each equation is eta-expanded
-- by adding as many variables as necessary to the argument list and
-- applying the right hand side to those variables (Note: eta-expansion
-- is disabled in the version for PAKCS).
-- Furthermore every occurrence of a record type within the type of a function
-- is simplified to the corresponding type constructor from the record
-- declaration. This is possible because currently records must not be empty
-- and a record label belongs to only one record declaration.

dsDeclRhs :: Decl -> DsM Decl
dsDeclRhs (FunctionDecl     p f eqs) = FunctionDecl p f <$> mapM dsEquation eqs
dsDeclRhs (PatternDecl      p t rhs) = PatternDecl  p t <$> dsRhs p id rhs
dsDeclRhs (ForeignDecl p cc ie f ty) = return $ ForeignDecl p cc ie' f ty
  where ie' = ie `mplus` Just (idName f)
dsDeclRhs fs@(FreeDecl          _ _) = return fs
dsDeclRhs _ = error "Desugar.dsDeclRhs: no pattern match"

dsEquation :: Equation -> DsM Equation
dsEquation (Equation p lhs rhs) = do
  funpats        <- desugarFunPats
  (ds1, cs, ts1) <- if funpats then do
                                  (     cs1, ts1) <- dsNonLinearity         ts
                                  (ds2, cs2, ts2) <- dsFunctionalPatterns p ts1
                                  return (ds2, cs2 ++ cs1, ts2)
                                else return ([], [], ts)
  (ds2    , ts2) <- mapAccumM (dsPattern p) [] ts1
  rhs'           <- dsRhs p (addConstraints cs) $ addDecls (ds1 ++ ds2) $ rhs
  return $ Equation p (FunLhs f ts2) rhs'
  where (f, ts) = flatLhs lhs

-- -----------------------------------------------------------------------------
-- Desugaring of non-linear patterns
-- -----------------------------------------------------------------------------

-- The desugaring traverses a pattern in depth-first order and collects
-- all variables. If it encounters a variable which has been previously
-- introduced, the second occurrence is changed to a fresh variable
-- and a new pair (newvar, oldvar) is saved to generate constraints later.
-- Non-linear patterns inside single functional patterns are not desugared,
-- as this special case is handled later.
dsNonLinearity :: [Pattern] -> DsM ([Expression], [Pattern])
dsNonLinearity ts = do
  ((_, cs), ts') <- mapAccumM dsNonLinear (Set.empty, []) ts
  return (reverse cs, ts')

type NonLinearEnv = (Set.Set Ident, [Expression])

dsNonLinear :: NonLinearEnv -> Pattern -> DsM (NonLinearEnv, Pattern)
dsNonLinear env l@(LiteralPattern        _) = return (env, l)
dsNonLinear env n@(NegativePattern     _ _) = return (env, n)
dsNonLinear env t@(VariablePattern       v)
  | isAnonId v         = return (env, t)
  | v `Set.member` vis = do
    v' <- freshMonoTypeVar "_#nonlinear" t
    return ((vis, mkStrictEquality v v' : eqs), VariablePattern v')
  | otherwise          = return ((Set.insert v vis, eqs), t)
  where (vis, eqs) = env
dsNonLinear env (ConstructorPattern   c ts) = second (ConstructorPattern c)
                                              <$> mapAccumM dsNonLinear env ts
dsNonLinear env (InfixPattern     t1 op t2) = do
  (env1, t1') <- dsNonLinear env  t1
  (env2, t2') <- dsNonLinear env1 t2
  return (env2, InfixPattern t1' op t2')
dsNonLinear env (ParenPattern            t) = second ParenPattern
                                              <$> dsNonLinear env t
dsNonLinear env (RecordPattern        c fs) =
  second (RecordPattern c) <$> mapAccumM (dsField dsNonLinear) env fs
dsNonLinear env (TuplePattern       pos ts) = second (TuplePattern pos)
                                              <$> mapAccumM dsNonLinear env ts
dsNonLinear env (ListPattern        pos ts) = second (ListPattern pos)
                                              <$> mapAccumM dsNonLinear env ts
dsNonLinear env (AsPattern             v t) = do
  (env1, VariablePattern v') <- dsNonLinear env  (VariablePattern v)
  (env2, t'                ) <- dsNonLinear env1 t
  return (env2, AsPattern v' t')
dsNonLinear env (LazyPattern           r t) = second (LazyPattern r)
                                          <$> dsNonLinear env t
dsNonLinear env fp@(FunctionPattern    _ _) = dsNonLinearFuncPat env fp
dsNonLinear env fp@(InfixFuncPattern _ _ _) = dsNonLinearFuncPat env fp

dsNonLinearFuncPat :: NonLinearEnv -> Pattern -> DsM (NonLinearEnv, Pattern)
dsNonLinearFuncPat (vis, eqs) fp = do
  let fpVars = bv fp
      vs     = filter (`Set.member` vis) fpVars
  vs' <- mapM (freshMonoTypeVar "_#nonlinear" . VariablePattern) vs
  let vis' = foldr Set.insert vis fpVars
      fp'  = substPat (zip vs vs') fp
  return ((vis', zipWith mkStrictEquality vs vs' ++ eqs), fp')

mkStrictEquality :: Ident -> Ident -> Expression
mkStrictEquality x y = mkVar x =:= mkVar y

substPat :: [(Ident, Ident)] -> Pattern -> Pattern
substPat _ l@(LiteralPattern        _) = l
substPat _ n@(NegativePattern     _ _) = n
substPat s (VariablePattern         v) = VariablePattern
                                       $ fromMaybe v (lookup v s)
substPat s (ConstructorPattern   c ps) = ConstructorPattern c
                                       $ map (substPat s) ps
substPat s (InfixPattern     p1 op p2) = InfixPattern (substPat s p1) op
                                                      (substPat s p2)
substPat s (ParenPattern            p) = ParenPattern (substPat s p)
substPat s (RecordPattern        c fs) = RecordPattern c (map substField fs)
  where substField (Field pos l pat) = Field pos l (substPat s pat)
substPat s (TuplePattern       pos ps) = TuplePattern pos $ map (substPat s) ps
substPat s (ListPattern        pos ps) = ListPattern  pos $ map (substPat s) ps
substPat s (AsPattern             v p) = AsPattern    (fromMaybe v (lookup v s))
                                                      (substPat s p)
substPat s (LazyPattern           r p) = LazyPattern r (substPat s p)
substPat s (FunctionPattern      f ps) = FunctionPattern f $ map (substPat s) ps
substPat s (InfixFuncPattern p1 op p2) = InfixFuncPattern (substPat s p1) op
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

dsFunctionalPatterns :: Position -> [Pattern]
                     -> DsM ([Decl], [Expression], [Pattern])
dsFunctionalPatterns p ts = do
  -- extract functional patterns
  (bs, ts') <- mapAccumM elimFP [] ts
  -- generate declarations of free variables and constraints
  let (ds, cs) = genFPExpr p (bv ts') (reverse bs)
  -- return (declarations, constraints, desugared patterns)
  return (ds, cs, ts')

type LazyBinding = (Pattern, Ident)

elimFP :: [LazyBinding] -> Pattern -> DsM ([LazyBinding], Pattern)
elimFP bs p@(LiteralPattern        _) = return (bs, p)
elimFP bs p@(NegativePattern     _ _) = return (bs, p)
elimFP bs p@(VariablePattern       _) = return (bs, p)
elimFP bs (ConstructorPattern   c ts) = second (ConstructorPattern c)
                                        <$> mapAccumM elimFP bs ts
elimFP bs (InfixPattern     t1 op t2) = do
  (bs1, t1') <- elimFP bs  t1
  (bs2, t2') <- elimFP bs1 t2
  return (bs2, InfixPattern t1' op t2')
elimFP bs (ParenPattern            t) = second ParenPattern <$> elimFP bs t
elimFP bs (RecordPattern        c fs) =
  second (RecordPattern c) <$> mapAccumM (dsField elimFP) bs fs
elimFP bs (TuplePattern       pos ts) = second (TuplePattern pos)
                                        <$> mapAccumM elimFP bs ts
elimFP bs (ListPattern        pos ts) = second (ListPattern pos)
                                        <$> mapAccumM elimFP bs ts
elimFP bs (AsPattern             v t) = second (AsPattern v) <$> elimFP bs t
elimFP bs (LazyPattern           r t) = second (LazyPattern r) <$> elimFP bs t
elimFP bs p@(FunctionPattern     _ _) = do
 v <- freshMonoTypeVar "_#funpatt" p
 return ((p, v) : bs, VariablePattern v)
elimFP bs p@(InfixFuncPattern  _ _ _) = do
 v <- freshMonoTypeVar "_#funpatt" p
 return ((p, v) : bs, VariablePattern v)

genFPExpr :: Position -> [Ident] -> [LazyBinding] -> ([Decl], [Expression])
genFPExpr p vs bs
  | null bs   = ([]               , [])
  | null free = ([]               , cs)
  | otherwise = ([FreeDecl p free], cs)
  where
  mkLB (t, v) = let (t', es) = fp2Expr t
                in  (t' =:<= mkVar v) : es
  cs       = concatMap mkLB bs
  free     = nub $ filter (not . isAnonId) $ bv (map fst bs) \\ vs

fp2Expr :: Pattern -> (Expression, [Expression])
fp2Expr (LiteralPattern          l) = (Literal l, [])
fp2Expr (NegativePattern       _ l) = (Literal (negateLiteral l), [])
fp2Expr (VariablePattern         v) = (mkVar v, [])
fp2Expr (ConstructorPattern   c ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (apply (Constructor c) ts', concat ess)
fp2Expr (InfixPattern     t1 op t2) =
  let (t1', es1) = fp2Expr t1
      (t2', es2) = fp2Expr t2
  in  (InfixApply t1' (InfixConstr op) t2', es1 ++ es2)
fp2Expr (ParenPattern            t) = first Paren (fp2Expr t)
fp2Expr (TuplePattern         r ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (Tuple r ts', concat ess)
fp2Expr (ListPattern         rs ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (List rs ts', concat ess)
fp2Expr (FunctionPattern      f ts) =
  let (ts', ess) = unzip $ map fp2Expr ts
  in  (apply (Variable f) ts', concat ess)
fp2Expr (InfixFuncPattern t1 op t2) =
  let (t1', es1) = fp2Expr t1
      (t2', es2) = fp2Expr t2
  in  (InfixApply t1' (InfixOp op) t2', es1 ++ es2)
fp2Expr (AsPattern             v t) =
  let (t', es) = fp2Expr t
  in  (mkVar v, (t' =:<= mkVar v):es)
fp2Expr t                           = internalError $
  "Desugar.fp2Expr: Unexpected constructor term: " ++ show t

-- -----------------------------------------------------------------------------
-- Desugaring of remaining patterns
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

dsPattern :: Position -> [Decl] -> Pattern -> DsM ([Decl], Pattern)
dsPattern _ ds v@(VariablePattern      _) = return (ds, v)
dsPattern p ds (LiteralPattern         l) = do
  dl <- dsLiteral l
  case dl of
    Left  l'     -> return (ds, LiteralPattern l')
    Right (rs,ls) -> dsPattern p ds $ ListPattern rs $ map LiteralPattern ls
dsPattern p ds (NegativePattern      _ l) =
  dsPattern p ds (LiteralPattern (negateLiteral l))
dsPattern p ds (ConstructorPattern c [t]) = do
    tyEnv <- getValueEnv
    (if isNewtypeConstr tyEnv c then id else second (constrPat c)) <$>
          (dsPattern p ds t)
  where constrPat c' t' = ConstructorPattern c' [t']
dsPattern p ds (ConstructorPattern  c ts) =
  second (ConstructorPattern c) <$> mapAccumM (dsPattern p) ds ts
dsPattern p ds (InfixPattern    t1 op t2) =
  dsPattern p ds (ConstructorPattern op [t1,t2])
dsPattern p ds (ParenPattern           t) = dsPattern p ds t
dsPattern p ds (RecordPattern      c  fs) = do
  tyEnv <- getValueEnv
  let ls = map (qualifyLike c) $ fst $ conType c tyEnv
      ts = map (dsLabel (VariablePattern anonId) (map field2Tuple fs)) ls
  dsPattern p ds (ConstructorPattern c ts)
dsPattern p ds (TuplePattern      pos ts) =
  dsPattern p ds (ConstructorPattern (tupleConstr ts) ts)
  where tupleConstr ts' = addRef pos $
                         if null ts' then qUnitId else qTupleId (length ts')
dsPattern p ds (ListPattern       pos ts) =
  second (dsList pos cons nil) <$> mapAccumM (dsPattern p) ds ts
  where nil  p' = ConstructorPattern (addRef p' qNilId) []
        cons p' t ts' = ConstructorPattern (addRef p' qConsId) [t,ts']
dsPattern p ds (AsPattern            v t) = dsAs p v <$> dsPattern p ds t
dsPattern p ds (LazyPattern          r t) = dsLazy r p ds t
dsPattern p ds (FunctionPattern     f ts) =
  second (FunctionPattern f) <$> mapAccumM (dsPattern p) ds ts
dsPattern p ds (InfixFuncPattern t1 f t2) =
  dsPattern p ds (FunctionPattern f [t1,t2])

dsLiteral :: Literal -> DsM (Either Literal ([SrcRef], [Literal]))
dsLiteral c@(Char             _ _) = return $ Left c
dsLiteral (Int                v i) = do
  tyEnv <- getValueEnv
  return (Left (fixType tyEnv))
  where fixType tyEnv'
          | typeOf tyEnv' v == floatType =
              Float (srcRefOf $ idPosition v) (fromIntegral i)
          | otherwise = Int v i
dsLiteral f@(Float            _ _) = return $ Left f
dsLiteral (String (SrcRef [i]) cs) = return $ Right
  (consRefs i cs, zipWith (Char . SrcRef . (:[])) [i, i + 2 ..] cs)
  where consRefs r []     = [SrcRef [r]]
        consRefs r (_:xs) = let r' = r + 2
                            in  r' `seq` (SrcRef [r'] : consRefs r' xs)
dsLiteral (String is _) = internalError $
  "Desugar.dsLiteral: " ++ "wrong source ref for string "  ++ show is

dsList :: [SrcRef] -> (SrcRef -> b -> b -> b) -> (SrcRef -> b) -> [b] -> b
dsList pos cons nil xs = snd (foldr cons' nil' xs)
  where rNil : rCs = reverse pos
        nil'                 = (rCs , nil rNil)
        cons' t (rC:rCs',ts) = (rCs', cons rC t ts)
        cons' _ ([],_) = error "Desugar.dsList.cons': empty list"

dsAs :: Position -> Ident -> ([Decl], Pattern) -> ([Decl], Pattern)
dsAs p v (ds, t) = case t of
  VariablePattern v' -> (varDecl p v (mkVar v') : ds, t)
  AsPattern     v' _ -> (varDecl p v (mkVar v') : ds, t)
  _                  -> (ds, AsPattern v t)

dsLazy :: SrcRef -> Position -> [Decl] -> Pattern -> DsM ([Decl], Pattern)
dsLazy pos p ds t = case t of
  VariablePattern   _ -> return (ds, t)
  ParenPattern     t' -> dsLazy pos p ds t'
  AsPattern      v t' -> dsAs p v <$> dsLazy pos p ds t'
  LazyPattern pos' t' -> dsLazy pos' p ds t'
  _                   -> do
   v' <- addPositionIdent (AST pos) <$> freshMonoTypeVar "_#lazy" t
   return (patDecl p { astRef = pos } t (mkVar v') : ds, VariablePattern v')

negateLiteral :: Literal -> Literal
negateLiteral (Int    v i) = Int   v  (-i)
negateLiteral (Float p' f) = Float p' (-f)
negateLiteral _            = internalError "Desugar.negateLiteral"

-- A list of boolean guards is expanded into a nested if-then-else
-- expression, whereas a constraint guard is replaced by a case
-- expression. Note that if the guard type is 'Success' only a
-- single guard is allowed for each equation (This change was
-- introduced in version 0.8 of the Curry report.). We check for the
-- type 'Bool' of the guard because the guard's type defaults to
-- 'Success' if it is not restricted by the guard expression.

dsRhs :: Position -> (Expression -> Expression) -> Rhs -> DsM Rhs
dsRhs p f rhs = do
  e' <- expandRhs prelFailed f rhs >>= dsExpr p
  return (SimpleRhs p e' [])

expandRhs :: Expression -> (Expression -> Expression) -> Rhs -> DsM Expression
expandRhs _  f (SimpleRhs _ e ds) = return $ Let ds (f e)
expandRhs e0 f (GuardedRhs es ds) = (Let ds . f) <$> expandGuards e0 es

expandGuards :: Expression -> [CondExpr] -> DsM Expression
expandGuards e0 es = do
  tyEnv <- getValueEnv
  return $ if booleanGuards tyEnv es
              then foldr mkIfThenElse e0 es
              else mkCond es
  where mkIfThenElse (CondExpr p g e) = IfThenElse (srcRefOf p) g e
        mkCond       [CondExpr _ g e] = apply prelCond [g, e]
        mkCond _ = error "Desugar.expandGuards.mkCond: non-unary list"

addConstraints :: [Expression] -> Expression -> Expression
addConstraints cs e
  | null cs   = e
  | otherwise = apply prelCond [foldr1 (&>) cs, e]

booleanGuards :: ValueEnv -> [CondExpr] -> Bool
booleanGuards _     []                    = False
booleanGuards tyEnv (CondExpr _ g _ : es) =
  not (null es) || typeOf tyEnv g == boolType

-- Record construction expressions are transformed into normal
-- constructor applications by rearranging fields in the order of the
-- record's declaration, passing `Prelude.undefined` in place of
-- omitted fields, and discarding the field labels. The transformation of
-- record update expressions is a bit more involved as we must match the
-- updated expression with all valid constructors of the expression's
-- type. As stipulated by the Haskell 98 Report, a record update
-- expression @e { l_1 = e_1, ..., l_k = e_k }@ succeeds only if @e@ reduces to
-- a value @C e'_1 ... e'_n@ such that @C@'s declaration contains all
-- field labels @l_1,...,l_k@. In contrast to Haskell we do not report
-- an error if this is not the case but rather fail only the current
-- solution.

dsExpr :: Position -> Expression -> DsM Expression
dsExpr p (Literal         l) =
  dsLiteral l >>=
  either (return . Literal) (\ (pos, ls) -> dsExpr p $ List pos $ map Literal ls)
dsExpr _ var@(Variable v)
  | isAnonId (unqualify v)   = return prelUnknown
  | otherwise                = return var
dsExpr _ c@(Constructor   _) = return c
dsExpr p (Paren           e) = dsExpr p e
dsExpr p (Typed        e ty) = Typed <$> dsExpr p e <*> dsTypeExpr ty
dsExpr p (Record       c fs) = do
  tyEnv <- getValueEnv
  let ls = map (qualifyLike c) $ fst $ conType c tyEnv
      es = map (dsLabel prelFailed (map field2Tuple fs)) ls
  dsExpr p $ apply (Constructor c) es
dsExpr p (RecordUpdate e fs) = do
  tcEnv <- getTyConsEnv
  ty    <- getTypeOf e
  let (TypeConstructor tc _) = arrowBase ty
  alts  <- mapM (updateAlt tc) (constructors tc tcEnv)
  dsExpr p $ Case (srcRefOf p) Flex e (map (uncurry (caseAlt p)) (concat alts))
  where
    ls = map fieldLabel fs
    updateAlt _   (DataConstr          _ _ _)          = return []
    updateAlt tc' (RecordConstr c _ labels tys)
      | all (`elem` (map (qualifyLike tc') labels)) ls = do
          vs <- mapM (freshIdent "_#rec" 0 . polyType) tys
          let qc  = qualifyLike tc' c
              qls = map (qualifyLike tc') labels
              es  = zipWith (\v l -> dsLabel (mkVar v) (map field2Tuple fs) l)
                      vs qls
          return [(constrPat qc vs, apply (Constructor qc) es)]
      | otherwise                             = return []
    constrPat qc' vs' = ConstructorPattern qc' (map VariablePattern vs')
dsExpr p (Tuple      pos es) = apply (Constructor $ tupleConstr es)
                             <$> mapM (dsExpr p) es
  where tupleConstr es1 = addRef pos
                        $ if null es1 then qUnitId else qTupleId (length es1)
dsExpr p (List       pos es) = dsList pos cons nil <$> mapM (dsExpr p) es
  where nil p'  = Constructor (addRef p' qNilId)
        cons p' = Apply . Apply (Constructor $ addRef p' qConsId)
dsExpr p (ListCompr    r e []    ) = dsExpr p (List [r,r] [e])
dsExpr p (ListCompr    r e (q:qs)) = dsQual p q (ListCompr r e qs)
dsExpr p (EnumFrom              e) = Apply prelEnumFrom <$> dsExpr p e
dsExpr p (EnumFromThen      e1 e2) = apply prelEnumFromThen
                                     <$> mapM (dsExpr p) [e1, e2]
dsExpr p (EnumFromTo        e1 e2) = apply prelEnumFromTo
                                     <$> mapM (dsExpr p) [e1, e2]
dsExpr p (EnumFromThenTo e1 e2 e3) = apply prelEnumFromThenTo
                                     <$> mapM (dsExpr p) [e1, e2, e3]
dsExpr p (UnaryMinus         op e) = do
  ty <- getTypeOf e
  e' <- dsExpr p e
  negativeLitsEnabled <- checkNegativeLitsExtension
  return $ case e' of
    Literal l | negativeLitsEnabled -> Literal $ negateLiteral l
    _                               -> Apply (unaryMinus op ty) e'
  where
  unaryMinus op1 ty'
    | op1 ==  minusId = if ty' == floatType then prelNegateFloat else prelNegate
    | op1 == fminusId = prelNegateFloat
    | otherwise       = internalError "Desugar.unaryMinus"
dsExpr p (Apply (Constructor c) e) = do
  tyEnv <- getValueEnv
  (if isNewtypeConstr tyEnv c then id else (Apply (Constructor c))) <$>
    dsExpr p e
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
  return $ apply prelFlip [op', e']
dsExpr p expr@(Lambda r ts e) = do
  ty <- getTypeOf expr
  f  <- freshIdent "_#lambda" (length ts) (polyType ty)
  dsExpr p $ Let [funDecl (AST r) f ts e] $ mkVar f
dsExpr p (Let ds e) = do
  ds' <- dsDeclGroup ds
  e'  <- dsExpr p e
  return (if null ds' then e' else Let ds' e')
dsExpr p (Do sts e) = dsExpr p (foldr desugarStmt e sts)
  where desugarStmt (StmtExpr r e1) e' = apply (prelBind_ r) [e1,e']
        desugarStmt (StmtBind r t e1) e' = apply (prelBind r) [e1,Lambda r [t] e']
        desugarStmt (StmtDecl ds) e' = Let ds e'
dsExpr p (IfThenElse r e1 e2 e3) = do
  e1' <- dsExpr p e1
  e2' <- dsExpr p e2
  e3' <- dsExpr p e3
  return $ Case r Rigid e1' [caseAlt p truePat e2', caseAlt p falsePat e3']
dsExpr p (Case r ct e alts)
  | null alts = return prelFailed
  | otherwise = do
    m  <- getModuleIdent
    e' <- dsExpr p e
    v  <- freshMonoTypeVar "_#case" e
    alts'  <- mapM dsAltLhs alts
    alts'' <- mapM (expandAlt v ct) (init (tails alts')) >>= mapM dsAltRhs
    return (mkCase m v e' alts'')
  where
  mkCase m1 v e1 alts1
    | v `elem` qfv m1 alts1 = Let [varDecl p v e1] (Case r ct (mkVar v) alts1)
    | otherwise             = Case r ct e1 alts1

dsLabel :: a -> [(QualIdent, a)] -> QualIdent -> a
dsLabel def fs l = fromMaybe def (lookup l fs)

dsField :: (a -> b -> DsM (a, b)) -> a -> Field b -> DsM (a, Field b)
dsField ds z (Field p l x) = do (z', x') <- ds z x
                                return (z', Field p l x')

dsTypeExpr :: TypeExpr -> DsM TypeExpr
dsTypeExpr ty = do
  tcEnv <- getTyConsEnv
  let expType = expandType tcEnv (toType [] ty)
  return $ fromType expType

expandType :: TCEnv -> Type -> Type
expandType tcEnv (TypeConstructor tc tys) = case qualLookupTC tc tcEnv of
  [DataType     tc' _  _] -> TypeConstructor tc' tys'
  [RenamingType tc' _  _] -> TypeConstructor tc' tys'
  [AliasType    _   _ ty] -> expandAliasType tys' ty
  _ -> internalError $ "Desugar.expandType " ++ show tc
  where tys' = map (expandType tcEnv) tys
expandType _     tv@(TypeVariable      _) = tv
expandType _     tc@(TypeConstrained _ _) = tc
expandType tcEnv (TypeArrow      ty1 ty2) =
  TypeArrow (expandType tcEnv ty1) (expandType tcEnv ty2)
expandType _     ts@(TypeSkolem        _) = ts

-- If an alternative in a case expression has boolean guards and all of
-- these guards return 'False', the enclosing case expression does
-- not fail but continues to match the remaining alternatives against the
-- selector expression. In order to implement this semantics, which is
-- compatible with Haskell, we expand an alternative with boolean guards
-- such that it evaluates a case expression with the remaining cases that
-- are compatible with the matched pattern when the guards fail.

dsAltLhs :: Alt -> DsM Alt
dsAltLhs (Alt p t rhs) = do
  (ds', t') <- dsPattern p [] t
  return $ Alt p t' (addDecls ds' rhs)

dsAltRhs :: Alt -> DsM Alt
dsAltRhs (Alt p t rhs) = Alt p t <$> dsRhs p id rhs

expandAlt :: Ident -> CaseType -> [Alt] -> DsM Alt
expandAlt _ _  []                   = error "Desugar.expandAlt: empty list"
expandAlt v ct (Alt p t rhs : alts) = caseAlt p t <$> expandRhs e0 id rhs
  where
  e0 | ct == Flex = prelFailed
     | otherwise  = Case (srcRefOf p) ct (mkVar v)
                         (filter (isCompatible t . altPattern) alts)
  altPattern (Alt _ t1 _) = t1

isCompatible :: Pattern -> Pattern -> Bool
isCompatible (VariablePattern _) _                   = True
isCompatible _                   (VariablePattern _) = True
isCompatible (AsPattern    _ t1) t2                  = isCompatible t1 t2
isCompatible t1                  (AsPattern    _ t2) = isCompatible t1 t2
isCompatible (ConstructorPattern c1 ts1) (ConstructorPattern c2 ts2)
  = and ((c1 == c2) : zipWith isCompatible ts1 ts2)
isCompatible (LiteralPattern         l1) (LiteralPattern         l2)
  = canon l1 == canon l2
  where canon (Int _ i) = Int anonId i
        canon l         = l
isCompatible _                    _                  = False

-- -----------------------------------------------------------------------------
-- Desugaring of Records
-- -----------------------------------------------------------------------------

-- As an extension to the Curry language the compiler supports Haskell's
-- record syntax, which introduces field labels for data and renaming
-- types. Field labels can be used in constructor declarations, patterns,
-- and expressions. For further convenience, an implicit selector
-- function is introduced for each field label.

-- Generate selection functions for record labels and replace record
-- constructor declarations by normal constructor declarations
dsRecordDecl :: Decl -> DsM [Decl]
dsRecordDecl (DataDecl p tc tvs cs) = do
  m  <- getModuleIdent
  let qcs = map (qualifyWith m . constrId) cs
  selFuns <- mapM (genSelectFunc p qcs) labels
  return $ DataDecl p tc tvs (map unlabelConstr cs) : selFuns
  where
    labels = nub $ concatMap recordLabels cs
dsRecordDecl (NewtypeDecl p tc tvs nc) = do
  m <- getModuleIdent
  let qc = qualifyWith m (nconstrId nc)
  selFun <- mapM (genSelectFunc p [qc]) (nrecordLabels nc)
  return $ NewtypeDecl p tc tvs (unlabelNewConstr nc) : selFun
dsRecordDecl d = return [d]

-- Generate selection function for a record label
genSelectFunc :: Position -> [QualIdent] -> Ident -> DsM Decl
genSelectFunc p qcs l = do
  eqs <- concat <$> mapM (selectorEqn l) qcs
  return $ FunctionDecl p l [funEqn l [pat] e | (pat, e) <- eqs]
  where
    funEqn f ps e = Equation p (FunLhs f ps) (SimpleRhs p e [])

-- Generate pattern and rhs for selection function
selectorEqn :: Ident -> QualIdent -> DsM [(Pattern, Expression)]
selectorEqn l qc = do
  tyEnv <- getValueEnv
  let (ls, ty) = conType qc tyEnv
      (tys, _) = arrowUnapply (instType ty)
  case elemIndex l ls of
    Just n  -> do vs <- mapM (freshIdent "_#rec" 0 . polyType) tys
                  let pvs = map VariablePattern vs
                      v   = qualify (vs !! n)
                  return [(ConstructorPattern qc pvs, Variable v)]
    Nothing -> return []

-- Transform record constructor declarations into normal declarations
unlabelConstr :: ConstrDecl -> ConstrDecl
unlabelConstr (RecordDecl p evs c fs) = ConstrDecl p evs c tys
  where tys = [ty | FieldDecl _ ls ty <- fs, _ <- ls]
unlabelConstr c                       = c

unlabelNewConstr :: NewConstrDecl -> NewConstrDecl
unlabelNewConstr (NewRecordDecl p evs nc (_, ty)) = NewConstrDecl p evs nc ty
unlabelNewConstr c                                = c

-- -----------------------------------------------------------------------------
-- Desugaring of List Comprehension
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

-- Actually, we generate slightly better code in a few special cases.
-- When 't' is a plain variable, the 'case' expression degenerates
-- into a let-binding and the auxiliary function thus becomes an alias
-- for '(++)'. Instead of 'foldr (++)' we use the
-- equivalent prelude function 'concatMap'. In addition, if the
-- remaining list comprehension in the body of the auxiliary function has
-- no qualifiers -- i.e., if it is equivalent to '[e]' -- we
-- avoid the construction of the singleton list by calling '(:)'
-- instead of '(++)' and 'map' in place of 'concatMap', respectively.

dsQual :: Position -> Statement -> Expression -> DsM Expression
dsQual p (StmtExpr   r b) e = dsExpr p (IfThenElse r b e (List [r] []))
dsQual p (StmtDecl    ds) e = dsExpr p (Let ds e)
dsQual p (StmtBind r t l) e
  | isVarPattern t = dsExpr p (qualExpr t e l)
  | otherwise      = do
    v   <- addRefId r <$> freshMonoTypeVar "_#var" t
    l'  <- addRefId r <$> freshMonoTypeVar "_#var" e
    dsExpr p (apply (prelFoldr r) [foldFunct v l' e, List [r] [], l])
  where
  qualExpr v (ListCompr _ e1 []) l1 = apply (prelMap       r)
                                      [Lambda r [v] e1, l1]
  qualExpr v e1                  l1 = apply (prelConcatMap r)
                                      [Lambda r [v] e1, l1]
  foldFunct v l1 e1
    = Lambda r (map VariablePattern [v,l1])
       (Case r Rigid (mkVar v)
          [ caseAlt p t (append e1 (mkVar l1))
          , caseAlt p (VariablePattern v) (mkVar l1)])

  append (ListCompr _ e1 []) l1 = apply prelCons       [e1, l1]
  append e1                  l1 = apply (prelAppend r) [e1, l1]
  prelCons                      = Constructor $ addRef r $ qConsId

-- ---------------------------------------------------------------------------
-- Prelude entities
-- ---------------------------------------------------------------------------

prelBind :: SrcRef -> Expression
prelBind = prel ">>="

prelBind_ :: SrcRef -> Expression
prelBind_ = prel ">>"

prelFlip :: Expression
prelFlip = Variable $ preludeIdent "flip"

prelEnumFrom :: Expression
prelEnumFrom = Variable $ preludeIdent "enumFrom"

prelEnumFromTo :: Expression
prelEnumFromTo = Variable $ preludeIdent "enumFromTo"

prelEnumFromThen :: Expression
prelEnumFromThen = Variable $ preludeIdent "enumFromThen"

prelEnumFromThenTo :: Expression
prelEnumFromThenTo = Variable $ preludeIdent "enumFromThenTo"

prelFailed :: Expression
prelFailed = Variable $ preludeIdent "failed"

prelUnknown :: Expression
prelUnknown = Variable $ preludeIdent "unknown"

prelMap :: SrcRef -> Expression
prelMap r = Variable $ addRef r $ preludeIdent "map"

prelFoldr :: SrcRef -> Expression
prelFoldr = prel "foldr"

prelAppend :: SrcRef -> Expression
prelAppend = prel "++"

prelConcatMap :: SrcRef -> Expression
prelConcatMap = prel "concatMap"

prelNegate :: Expression
prelNegate = Variable $ preludeIdent "negate"

prelNegateFloat :: Expression
prelNegateFloat = Variable $ preludeIdent "negateFloat"

prelCond :: Expression
prelCond = Variable $ preludeIdent "cond"

(=:<=) :: Expression -> Expression -> Expression
e1 =:<= e2 = apply prelFPEq [e1, e2]

prelFPEq :: Expression
prelFPEq = Variable $ preludeIdent "=:<="

(=:=) :: Expression -> Expression -> Expression
e1 =:= e2 = apply prelSEq [e1, e2]

prelSEq :: Expression
prelSEq = Variable $ preludeIdent "=:="

(&>) :: Expression -> Expression -> Expression
e1 &> e2 = apply prelCond [e1, e2]

prel :: String -> SrcRef -> Expression
prel s r = Variable $ addRef r $ preludeIdent s

truePat :: Pattern
truePat = ConstructorPattern qTrueId []

falsePat :: Pattern
falsePat = ConstructorPattern qFalseId []

preludeIdent :: String -> QualIdent
preludeIdent = qualifyWith preludeMIdent . mkIdent

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
isNewtypeConstr tyEnv c = case qualLookupValue c tyEnv of
  [NewtypeConstructor _ _ _] -> True
  [DataConstructor  _ _ _ _] -> False
  x -> internalError $ "Transformations.Desugar.isNewtypeConstr: "
                        ++ show c ++ " is " ++ show x

isVarPattern :: Pattern -> Bool
isVarPattern (VariablePattern _) = True
isVarPattern (ParenPattern    t) = isVarPattern t
isVarPattern (AsPattern     _ t) = isVarPattern t
isVarPattern (LazyPattern   _ _) = True
isVarPattern _                   = False

funDecl :: Position -> Ident -> [Pattern] -> Expression -> Decl
funDecl p f ts e = FunctionDecl p f
  [Equation p (FunLhs f ts) (SimpleRhs p e [])]

patDecl :: Position -> Pattern -> Expression -> Decl
patDecl p t e = PatternDecl p t (SimpleRhs p e [])

varDecl :: Position -> Ident -> Expression -> Decl
varDecl p = patDecl p . VariablePattern

addDecls :: [Decl] -> Rhs -> Rhs
addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

caseAlt :: Position -> Pattern -> Expression -> Alt
caseAlt p t e = Alt p t (SimpleRhs p e [])

apply :: Expression -> [Expression] -> Expression
apply = foldl Apply

mkVar :: Ident -> Expression
mkVar = Variable . qualify

-- The function 'instType' instantiates the universally quantified
-- type variables of a type scheme with fresh type variables. Since this
-- function is used only to instantiate the closed types of record
-- constructors (Recall that no existentially quantified type
-- variables are allowed for records), the compiler can reuse the same
-- monomorphic type variables for every instantiated type.

instType :: ExistTypeScheme -> Type
instType (ForAllExist _ _ ty) = inst ty
  where inst (TypeConstructor tc tys) = TypeConstructor tc (map inst tys)
        inst (TypeVariable        tv) = TypeVariable (-1 - tv)
        inst (TypeArrow      ty1 ty2) = TypeArrow (inst ty1) (inst ty2)
        inst ty'                      = ty'

constructors :: QualIdent -> TCEnv -> [DataConstr]
constructors c tcEnv = case qualLookupTC c tcEnv of
  [DataType     _ _ cs] -> cs
  [RenamingType _ _ nc] -> [nc]
  _                     -> internalError $
    "Transformations.Desugar.constructors: " ++ show c
