{- |
    Module      :  $Header$
    Description :  Optimizing the Desugared Code
    Copyright   :  (c) 2003        Wolfgang Lux
                                   Martin Engelke
                       2011 - 2015 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After desugaring the source code, but before lifting local
   declarations, the compiler performs a few simple optimizations to
   improve the efficiency of the generated code. In addition, the
   optimizer replaces pattern bindings with simple variable bindings and
   selector functions.

   Currently, the following optimizations are implemented:

     * Under certain conditions, inline local function definitions.
     * Remove unused declarations.
     * Compute minimal binding groups for let expressions.
     * Remove pattern bindings to constructor terms
     * Inline simple constants.
-}
{-# LANGUAGE CPP #-}
module Transformations.Simplify (simplify) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad.State as S   (State, runState, gets, modify)
import qualified Data.Map            as Map (Map, empty, insert, lookup)

import Curry.Base.Position
import Curry.Base.Ident
import Curry.Syntax

import Base.Expr
import Base.Messages (internalError)
import Base.SCC
import Base.Types
import Base.Typing
import Base.Utils (concatMapM)

import Env.Value (ValueEnv, ValueInfo (..), bindFun, qualLookupValue)

-- -----------------------------------------------------------------------------
-- Simplification
-- -----------------------------------------------------------------------------

simplify :: ValueEnv -> Module -> (Module, ValueEnv)
simplify tyEnv mdl@(Module _ m _ _ _) = (mdl', valueEnv s')
  where (mdl', s') = S.runState (simModule mdl) (SimplifyState m tyEnv 1)

-- -----------------------------------------------------------------------------
-- Internal state monad
-- -----------------------------------------------------------------------------

data SimplifyState = SimplifyState
  { moduleIdent :: ModuleIdent -- read-only!
  , valueEnv    :: ValueEnv    -- updated for new pattern selection functions
  , nextId      :: Int         -- counter
  }

type SIM = S.State SimplifyState

getModuleIdent :: SIM ModuleIdent
getModuleIdent = S.gets moduleIdent

getNextId :: SIM Int
getNextId = do
  nid <- S.gets nextId
  S.modify $ \s -> s { nextId = succ nid }
  return nid

getTypeOf :: Typeable t => t -> SIM Type
getTypeOf t = do
  tyEnv <- getValueEnv
  return (typeOf tyEnv t)

getFunArity :: QualIdent -> SIM Int
getFunArity f = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  return $ case qualLookupValue f tyEnv of
    [Value _ _ (ForAll _ ty)] -> arrowArity ty
    _                         -> case qualLookupValue (qualQualify m f) tyEnv of
      [Value _ _ (ForAll _ ty)] -> arrowArity ty
      _                         -> internalError $ "Simplify.funType " ++ show f

modifyValueEnv :: (ValueEnv -> ValueEnv) -> SIM ()
modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

getValueEnv :: SIM ValueEnv
getValueEnv = S.gets valueEnv

freshIdent :: (Int -> Ident) -> TypeScheme -> SIM Ident
freshIdent f ty@(ForAll _ t) = do
  m <- getModuleIdent
  x <- f <$> getNextId
  modifyValueEnv $ bindFun m x (arrowArity t) ty
  return x

-- -----------------------------------------------------------------------------
-- Simplification
-- -----------------------------------------------------------------------------

simModule :: Module -> SIM Module
simModule (Module ps m es is ds) = Module ps m es is
                                   <$> mapM (simDecl Map.empty) ds

-- Inline an expression for a variable
type InlineEnv = Map.Map Ident Expression

simDecl :: InlineEnv -> Decl -> SIM Decl
simDecl env (FunctionDecl p f eqs) = FunctionDecl p f
                                     <$> concatMapM (simEquation env) eqs
simDecl env (PatternDecl  p t rhs) = PatternDecl  p t <$> simRhs env rhs
simDecl _   d                      = return d

simEquation :: InlineEnv -> Equation -> SIM [Equation]
simEquation env (Equation p lhs rhs) = do
  rhs'  <- simRhs env rhs
  inlineFun env p lhs rhs'

simRhs :: InlineEnv -> Rhs -> SIM Rhs
simRhs env (SimpleRhs p e _) = simpleRhs p <$> simExpr env e
simRhs _   (GuardedRhs  _ _) = error "Simplify.simRhs: guarded rhs"

-- -----------------------------------------------------------------------------
-- Inlining of Functions
-- -----------------------------------------------------------------------------

-- After simplifying the right hand side of an equation, the compiler
-- transforms declarations of the form
--
--   f t_1 ... t_{k-l} x_{k-l+1} ... x_k =
--     let g y_1 ... y_l = e
--     in  g x_{k-l+1} ... x_k
--
-- into the equivalent definition
--
--   f t_1 ... t_{k-l} x_{k-l+1} x_k = let y_1   = x_{k-l+1}
--                                              ...
--                                         y_l   = x_k
--                                     in  e
--
-- where the arities of 'f' and 'g' are 'k' and 'l', respectively, and
-- 'x_{k-l+1}, ... ,x_k' are variables. The transformation can obviously be
-- generalized to the case where 'g' is defined by more than one equation.
-- However, we must be careful not to change the evaluation mode of arguments.
-- Therefore, the transformation is applied only all of the arguments of 'g'
-- are variables.
--
-- This transformation is actually just a special case of inlining a
-- (local) function definition. We are unable to handle the general case
-- because it would require to represent the pattern matching code
-- explicitly in a Curry expression.

inlineFun :: InlineEnv -> Position -> Lhs -> Rhs -> SIM [Equation]
inlineFun env p lhs rhs = do
  m <- getModuleIdent
  case rhs of
    SimpleRhs _ (Let [FunctionDecl _ f' eqs'] e) _
      | -- @f'@ is not recursive
        f' `notElem` qfv m eqs'
        -- @f'@ does not perform any pattern matching
        && and [all isVarPattern ts1 | Equation _ (FunLhs _ ts1) _ <- eqs']
      -> do
        a <- getFunArity (qualify f')
        let (n, vs', e') = etaReduce 0 [] (reverse (snd $ flatLhs lhs)) e
        if  -- the eta-reduced rhs of @f@ is a call to @f'@
            e' == Variable (qualify f')
            -- @f'@ was fully applied before eta-reduction
            && n  == a
          then mapM (mergeEqns p vs') eqs'
          else return [Equation p lhs rhs]
    _ -> return [Equation p lhs rhs]
  where
  etaReduce n1 vs (VariablePattern v : ts1) (Apply e1 (Variable v'))
    | qualify v == v' = etaReduce (n1 + 1) (v:vs) ts1 e1
  etaReduce n1 vs _ e1 = (n1, vs, e1)

  mergeEqns p1 vs (Equation _ (FunLhs _ ts2) (SimpleRhs p2 e _))
    = Equation p1 lhs <$> simRhs env (simpleRhs p2 (Let ds e))
      where
      ds = zipWith (\t v -> PatternDecl p2 t (simpleRhs p2 (mkVar v))) ts2 vs
  mergeEqns _ _ _ = error "Simplify.inlineFun.mergeEqns: no pattern match"

-- -----------------------------------------------------------------------------
-- Simplification of Expressions
-- -----------------------------------------------------------------------------

-- Variables that are bound to (simple) constants and aliases to other
-- variables are substituted. In terms of conventional compiler technology,
-- these optimizations correspond to constant propagation and copy propagation,
-- respectively. The transformation is applied recursively to a substituted
-- variable in order to handle chains of variable definitions.

-- Applications of let-expressions and case-expressions to other expressions
-- are simplified according to the following rules:
--   (let ds in e_1)            e_2 -> let ds in (e1 e2)
--   (case e_1 of p'_n -> e'_n) e_2 -> case e_1 of p'_n -> (e'n e_2)

-- The bindings of a let expression are sorted topologically in
-- order to split them into minimal binding groups. In addition,
-- local declarations occurring on the right hand side of a pattern
-- declaration are lifted into the enclosing binding group using the
-- equivalence (modulo alpha-conversion) of 'let x = let ds in e_1 in e_2'
-- and 'let ds; x = e_1 in e_2'.
-- This transformation avoids the creation of some redundant lifted
-- functions in later phases of the compiler.

simExpr :: InlineEnv -> Expression -> SIM Expression
simExpr _   l@(Literal     _) = return l
simExpr _   c@(Constructor _) = return c
-- subsitution of variables
simExpr env v@(Variable    x)
  | isQualified x = return v
  | otherwise     = maybe (return v) (simExpr env) (Map.lookup (unqualify x) env)
-- simplification of application
simExpr env (Apply     e1 e2) = case e1 of
  Let ds e'       -> simExpr env (Let ds (Apply e' e2))
  Case r ct e' bs -> simExpr env (Case r ct e' (map (applyToAlt e2) bs))
  _               -> Apply <$> simExpr env e1 <*> simExpr env e2
  where
  applyToAlt e (Alt       p t rhs) = Alt p t (applyToRhs e rhs)
  applyToRhs e (SimpleRhs p e1' _) = simpleRhs p (Apply e1' e)
  applyToRhs _ (GuardedRhs    _ _) = error "Simplify.simExpr.applyRhs: Guarded rhs"
-- simplification of declarations
simExpr env (Let        ds e) = do
  m   <- getModuleIdent
  dss <- mapM sharePatternRhs ds
  simplifyLet env (scc bv (qfv m) (foldr hoistDecls [] (concat dss))) e
simExpr env (Case  r ct e bs) = Case r ct     <$> simExpr env e
                                              <*> mapM (simplifyAlt env) bs
simExpr env (Typed      e ty) = flip Typed ty <$> simExpr env e
simExpr _   _                 = error "Simplify.simExpr: no pattern match"

-- Simplify a case alternative
simplifyAlt :: InlineEnv -> Alt -> SIM Alt
simplifyAlt env (Alt p t rhs) = Alt p t <$> simRhs env rhs

-- Transform a pattern declaration @t = e@ into two declarations
-- @t = v, v = e@ whenever @t@ is not a variable. This is used to share
-- the expression @e@.
sharePatternRhs :: Decl -> SIM [Decl]
sharePatternRhs (PatternDecl p t rhs) = case t of
  VariablePattern _ -> return [PatternDecl p t rhs]
  _                 -> do
    ty <- monoType <$> getTypeOf t
    v  <- addRefId (srcRefOf p) <$> freshIdent patternId ty
    return [ PatternDecl p t                   (simpleRhs p (mkVar v))
           , PatternDecl p (VariablePattern v) rhs
           ]
  where patternId n = mkIdent ("_#pat" ++ show n)
sharePatternRhs d                     = return [d]

-- Lift up nested let declarations in pattern declarations, i.e., replace
-- @let p = let ds' in e'; ds in e@ by @let ds'; p = e'; ds in e@.
hoistDecls :: Decl -> [Decl] -> [Decl]
hoistDecls (PatternDecl p t (SimpleRhs p' (Let ds' e) _)) ds
 = foldr hoistDecls ds (PatternDecl p t (simpleRhs p' e) : ds')
hoistDecls d ds = d : ds

-- The declaration groups of a let expression are first processed from
-- outside to inside, simplifying the right hand sides and collecting
-- inlineable expressions on the fly. At present, only simple constants
-- and aliases to other variables are inlined. A constant is considered
-- simple if it is either a literal, a constructor, or a non-nullary
-- function. Note that it is not possible to define nullary functions in
-- local declarations in Curry. Thus, an unqualified name always refers
-- to either a variable or a non-nullary function. Applications of
-- constructors and partial applications of functions to at least one
-- argument are not inlined because the compiler has to allocate space
-- for them, anyway. In order to prevent non-termination, recursive
-- binding groups are not processed for inlining.

-- With the list of inlineable expressions, the body of the let is
-- simplified and then the declaration groups are processed from inside
-- to outside to construct the simplified, nested let expression. In
-- doing so, unused bindings are discarded. In addition, all pattern
-- bindings are replaced by simple variable declarations using selector
-- functions to access the pattern variables.

simplifyLet :: InlineEnv -> [[Decl]] -> Expression -> SIM Expression
simplifyLet env []       e = simExpr env e
simplifyLet env (ds:dss) e = do
  m     <- getModuleIdent
  ds'   <- mapM (simDecl env) ds  -- simplify declarations
  env'  <- inlineVars env ds'     -- inline a simple variable binding
  e'    <- simplifyLet env' dss e -- simplify remaining bindings
  ds''  <- concatMapM (expandPatternBindings (qfv m ds' ++ qfv m e')) ds'
  return $ foldr (mkLet m) e' (scc bv (qfv m) ds'')

inlineVars :: InlineEnv -> [Decl] -> SIM InlineEnv
inlineVars env ds = case ds of
  [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] -> do
    allowed <- canInlineVar v e
    return $ if allowed then Map.insert v e env else env
  _ -> return env
  where
  canInlineVar _ (Literal     _) = return True
  canInlineVar _ (Constructor _) = return True
  canInlineVar v (Variable   v')
    | isQualified v'             = (> 0) <$> getFunArity v'
    | otherwise                  = return $ v /= unqualify v'
  canInlineVar _ _               = return False

mkLet :: ModuleIdent -> [Decl] -> Expression -> Expression
mkLet m [FreeDecl p vs] e
  | null vs'  = e
  | otherwise = Let [FreeDecl p vs'] e         -- remove unused free variables
  where vs' = filter (`elem` qfv m e) vs
mkLet m [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] (Variable v')
  | v' == qualify v && v `notElem` qfv m e = e -- inline single binding
mkLet m ds e
  | null (filter (`elem` qfv m e) (bv ds)) = e -- removed unused bindings
  | otherwise                              = Let ds e

-- In order to implement lazy pattern matching in local declarations,
-- pattern declarations 't = e' where 't' is not a variable
-- are transformed into a list of declarations
-- 'v_0 = e; v_1 = f_1 v_0; ...; v_n = f_n v_0' where 'v_0' is a fresh
-- variable, 'v_1,...,v_n' are the variables occurring in 't' and the
-- auxiliary functions 'f_i' are defined by 'f_i t = v_i' (see also
-- appendix D.8 of the Curry report). The bindings 'v_0 = e' are introduced
-- before splitting the declaration groups of the enclosing let expression
-- (cf. the 'Let' case in 'simExpr' above) so that they are placed in their own
-- declaration group whenever possible. In particular, this ensures that
-- the new binding is discarded when the expression 'e' is itself a variable.

-- fvs contains all variables used in the declarations and the body
-- of the let expression.
expandPatternBindings :: [Ident] -> Decl -> SIM [Decl]
expandPatternBindings fvs d@(PatternDecl p t (SimpleRhs _ e _)) = case t of
  VariablePattern _ -> return [d]
  _                 -> do
  pty <- getTypeOf t -- type of pattern
  mapM (mkSelectorDecl pty) (filter (`elem` fvs) (bv t)) -- used variables
 where
  mkSelectorDecl pty v = do
    vty <- getTypeOf v
    f   <- freshIdent (updIdentName (++ '#' : idName v) . fpSelectorId)
                      (polyType (TypeArrow pty vty))
    return $ varDecl p v $ Let [funDecl p f [t] (mkVar v)] (Apply (mkVar f) e)
expandPatternBindings _ d = return [d]

-- ---------------------------------------------------------------------------
-- Auxiliary functions
-- ---------------------------------------------------------------------------

isVarPattern :: Pattern -> Bool
isVarPattern (VariablePattern      _) = True
isVarPattern (AsPattern          _ t) = isVarPattern t
isVarPattern (ConstructorPattern _ _) = False
isVarPattern (LiteralPattern       _) = False
isVarPattern _ = error "Simplify.isVarPattern: no pattern match"

mkVar :: Ident -> Expression
mkVar = Variable . qualify

simpleRhs :: Position -> Expression -> Rhs
simpleRhs p e = SimpleRhs p e []

varDecl :: Position -> Ident -> Expression -> Decl
varDecl p v e = PatternDecl p (VariablePattern v) (simpleRhs p e)

funDecl :: Position -> Ident -> [Pattern] -> Expression -> Decl
funDecl p f ts e = FunctionDecl p f [Equation p (FunLhs f ts) (simpleRhs p e)]

-- ---------------------------------------------------------------------------
-- Additional information
-- ---------------------------------------------------------------------------

-- Unfortunately, the transformation of pattern declarations introduces a
-- well-known space leak (Wadler87:Leaks,Sparud93:Leaks) because the matched
-- expression cannot be garbage collected until all of the matched
-- variables have been evaluated. Consider the following function:
--
--   f x | all (' ' ==) cs = c where (c:cs) = x
--
-- One might expect the call 'f (replicate 10000 ' ')' to execute in
-- constant space because (the tail of) the long list of blanks is
-- consumed and discarded immediately by 'all'. However, the
-- application of the selector function that extracts the head of the
-- list is not evaluated until after the guard has succeeded and thus
-- prevents the list from being garbage collected.

-- In order to avoid this space leak we use the approach
-- from (Sparud93:Leaks) and update all pattern variables when one
-- of the selector functions has been evaluated. Therefore, all pattern
-- variables except for the matched one are passed as additional
-- arguments to each of the selector functions. Thus, each of these
-- variables occurs twice in the argument list of a selector function,
-- once in the first argument and also as one of the remaining arguments.
-- This duplication of names is used by the compiler to insert the code
-- that updates the variables when generating abstract machine code.

-- By its very nature, this transformation introduces cyclic variable
-- bindings. Since cyclic bindings are not supported by PAKCS, we revert
-- to a simpler translation when generating FlatCurry output.

-- We will add only those pattern variables as additional arguments which
-- are actually used in the code. This reduces the number of auxiliary
-- variables and can prevent the introduction of a recursive binding
-- group when only a single variable is used. It is also the reason for
-- performing this transformation here instead of in the 'Desugar' module.
-- The selector functions are defined in a local declaration on
-- the right hand side of a projection declaration so that there is
-- exactly one declaration for each used variable.

-- Another problem of the translation scheme is the handling of pattern
-- variables with higher-order types, e.g.,
--
--   strange :: [a->a] -> Maybe (a->a)
--   strange xs = Just x
--     where (x:_) = xs
--
-- By reusing the types of the pattern variables, the selector function
-- 'f (x:_) = x' has type '[a->a] -> a -> a' and therefore seems to be
-- a binary function. Thus, in the goal 'strange []' the
-- selector is only applied partially and not evaluated. Note that this
-- goal will fail without the type annotation. In order to ensure that a
-- selector function is always evaluated when the corresponding variable
-- is used, we assume that the projection declarations -- ignoring the
-- additional arguments to prevent the space leak -- are actually defined
-- by 'f_i t = I v_i', using a private renaming type
--
--   newtype Identity a = I a
--
-- As newtype constructors are completely transparent to the compiler,
-- this does not change the generated code, but only the types of the
-- selector functions.

-- identityType :: Type -> Type
-- identityType = TypeConstructor qIdentityId . return
--   where qIdentityId = qualify (mkIdent "Identity")
