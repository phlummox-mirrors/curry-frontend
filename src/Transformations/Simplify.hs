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

     * Remove unused declarations.
     * Inline simple constants.
     * Compute minimal binding groups.
     * Under certain conditions, inline local function definitions.
-}

module Transformations.Simplify (simplify) where

import           Control.Applicative
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

data SimplifyState = SimplifyState
  { moduleIdent :: ModuleIdent -- read-only!
  , valueEnv    :: ValueEnv
  , nextId      :: Int         -- counter
  }

type SIM = S.State SimplifyState

-- Inline an expression for a variable
type InlineEnv = Map.Map Ident Expression

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

modifyValueEnv :: (ValueEnv -> ValueEnv) -> SIM ()
modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

getValueEnv :: SIM ValueEnv
getValueEnv = S.gets valueEnv

simplify :: ValueEnv -> Module -> (Module, ValueEnv)
simplify tyEnv mdl@(Module _ m _ _ _) = (mdl', valueEnv s')
  where (mdl', s') = S.runState (simModule mdl) (SimplifyState m tyEnv 1)

simModule :: Module -> SIM Module
simModule (Module ps m es is ds) = Module ps m es is
                                   <$> mapM (simDecl Map.empty) ds

simDecl :: InlineEnv -> Decl -> SIM Decl
simDecl env (FunctionDecl p f eqs) = FunctionDecl p f
                                     <$> concatMapM (simEquation env) eqs
simDecl env (PatternDecl  p t rhs) = PatternDecl  p t <$> simRhs env rhs
simDecl _   d                      = return d

-- After simplifying the right hand side of an equation, the compiler
-- transforms declarations of the form
--
--   f t_1 ... t_{k-k'} x_{k-k'+1} ... x_k =
--     let f' t'_1 ... t'_k' = e
--     in f' x_1 ... x_k'
--
-- into the equivalent definition
--
--   f t_1 ... t_{k-k'} (x_{k-k'+1}@t'_1) ... (x_k@t'_k' = e
--
-- where the arities of 'f' and 'f'' are 'k' and 'k'', respectively, and
-- 'x_{k-k'+1}, ... ,x_k' are variables. This optimization was
-- introduced in order to avoid an auxiliary function being generated for
-- definitions whose right-hand side is a lambda-expression, e.g.,
-- 'f . g = \x -> f (g x)'. This declaration is transformed into
-- '(.) f g x = let lambda x = f (g x) in lambda x' by desugaring
-- and in turn is optimized into '(.) f g x = f (g x)', here. The
-- transformation can obviously be generalized to the case where 'f'' is
-- defined by more than one equation. However, we must be careful not to
-- change the evaluation mode of arguments. Therefore, the transformation
-- is applied only if 'f' and 'f'' use them same evaluation mode or all
-- of the arguments 't'_1,...,t'_k' are variables. Actually, the
-- transformation could be applied to the case where the arguments
-- 't_1,...,t_{k-k'}' are all variables as well, but in this case the
-- evaluation mode of 'f' may have to be changed to match that of 'f''.

-- We have to be careful with this optimization in conjunction with
-- newtype constructors. It is possible that the local function is
-- applied only partially, e.g., for
--
--   newtype ST s a = ST (s -> (a,s))
--   returnST x = ST (\s -> (x,s))
--
-- the desugared code is equivalent to
--
--   returnST x = let lambda1 s = (x,s) in lambda1
--
-- We must not optimize this into 'returnST x s = (x,s)'
-- because the compiler assumes that 'returnST' is a unary
-- function.

-- Note that this transformation is not strictly semantic preserving as
-- the evaluation order of arguments can be changed. This happens if 'f'
-- is defined by more than one rule with overlapping patterns and the
-- local functions of each rule have disjoint patterns. As an example,
-- consider the function
--
--   f (Just x) _ = let g (Left z)  = x + z in g
--   f _ (Just y) = let h (Right z) = y + z in h
--
-- The definition of 'f' is non-deterministic because of the
-- overlapping patterns in the first and second argument. However, the
-- optimized definition
--
--   f (Just x) _ (Left z)  = x + z
--   f _ (Just y) (Right z) = y + z
--
-- is deterministic. It will evaluate and match the third argument first,
-- whereas the original definition is going to evaluate the first or the
-- second argument first, depending on the non-deterministic branch
-- chosen. As such definitions are presumably rare, and the optimization
-- avoids a non-deterministic split of the computation, we put up with
-- the change of evaluation order.

-- This transformation is actually just a special case of inlining a
-- (local) function definition. We are unable to handle the general case
-- because it would require to represent the pattern matching code
-- explicitly in a Curry expression.

simEquation :: InlineEnv -> Equation -> SIM [Equation]
simEquation env (Equation p lhs rhs) = do
  m     <- getModuleIdent
  rhs'  <- simRhs env rhs
  tyEnv <- getValueEnv
  return $ inlineFun m tyEnv p lhs rhs'

inlineFun :: ModuleIdent -> ValueEnv -> Position -> Lhs -> Rhs -> [Equation]
inlineFun m tyEnv p (FunLhs f ts) (SimpleRhs _ (Let [FunctionDecl _ f' eqs'] e) _)
-- TODO: understand this
  | True -- False -- inlining of functions is deactivated (hsi)
   && f' `notElem` qfv m eqs' && e' == Variable (qualify f') &&
    n == arrowArity (funType m tyEnv (qualify f')) &&
     and [all isVarPattern ts1 | Equation _ (FunLhs _ ts1) _ <- eqs']
  = map (mergeEqns p f ts' vs') eqs'
  where
  (n,vs',ts',e') = etaReduce 0 [] (reverse ts) e

  etaReduce n1 vs (VariablePattern v : ts1) (Apply e1 (Variable v'))
    | qualify v == v' = etaReduce (n1 + 1) (v:vs) ts1 e1
  etaReduce n1 vs ts1 e1 = (n1,vs,reverse ts1,e1)

  mergeEqns p1 f1 ts1 vs (Equation _ (FunLhs _ ts2) rhs) =
    Equation p1 (FunLhs f1 (ts1 ++ zipWith AsPattern vs ts2)) rhs
  mergeEqns _ _ _ _ _ = error "Simplify.inlineFun.mergeEqns: no pattern match"
inlineFun _ _ p lhs rhs = [Equation p lhs rhs]

simRhs :: InlineEnv -> Rhs -> SIM Rhs
simRhs env (SimpleRhs p e _) = (\ e' -> SimpleRhs p e' []) <$> simExpr env e
simRhs _   (GuardedRhs  _ _) = error "Simplify.simRhs: guarded rhs"

-- Variables that are bound to (simple) constants and aliases to other
-- variables are substituted. In terms of conventional compiler
-- technology these optimizations correspond to constant folding and copy
-- propagation, respectively. The transformation is applied recursively
-- to a substituted variable in order to handle chains of variable
-- definitions.

-- The bindings of a let expression are sorted topologically in
-- order to split them into minimal binding groups. In addition,
-- local declarations occurring on the right hand side of a pattern
-- declaration are lifted into the enclosing binding group using the
-- equivalence (modulo alpha-conversion) of 'let x  = let decls in e_1 in e_2'
-- and 'let decls; x = e_1 in e_2'.
-- This transformation avoids the creation of some redundant lifted
-- functions in later phases of the compiler.

simExpr :: InlineEnv -> Expression -> SIM Expression
simExpr _   l@(Literal     _) = return l
simExpr _   c@(Constructor _) = return c
simExpr env v@(Variable    x)
  | isQualified x = return v
  | otherwise     = maybe (return v) (simExpr env) (Map.lookup (unqualify x) env)
simExpr env (Apply     e1 e2) = case e1 of
  Let ds e'       -> simExpr env $ Let ds (Apply e' e2)
  Case r ct e' bs -> simExpr env $ Case r ct e' (map (applyToAlt e2) bs)
  _               -> Apply <$> simExpr env e1 <*> simExpr env e2
  where
  applyToAlt e (Alt       p t rhs) = Alt p t (applyToRhs e rhs)
  applyToRhs e (SimpleRhs p e1' _) = SimpleRhs p (Apply e1' e) []
  applyToRhs _ (GuardedRhs    _ _) = error "Simplify.simExpr.applyRhs: Guarded rhs"
simExpr env (Let        ds e) = do
  m    <- getModuleIdent
  dss' <- mapM sharePatternRhs ds
  simplifyLet env (scc bv (qfv m) (foldr hoistDecls [] (concat dss'))) e
simExpr env (Case  r ct e bs) = Case r ct     <$> simExpr env e
                                              <*> mapM (simplifyAlt env) bs
simExpr env (Typed      e ty) = flip Typed ty <$> simExpr env e
simExpr _   _                 = error "Simplify.simExpr: no pattern match"

simplifyAlt :: InlineEnv -> Alt -> SIM Alt
simplifyAlt env (Alt p t rhs) = Alt p t <$> simRhs env rhs

-- Lift up nested let declarations.
hoistDecls :: Decl -> [Decl] -> [Decl]
hoistDecls (PatternDecl p t (SimpleRhs p' (Let ds e) _)) ds'
 = foldr hoistDecls ds' (PatternDecl p t (SimpleRhs p' e []) : ds)
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
  ds'   <- mapM (simDecl env) ds  -- simplify right-hand sides
  env'  <- inlineVars  ds'  env   -- inline a simple variable binding
  e'    <- simplifyLet env' dss e -- simplify remaining bindings
  m     <- getModuleIdent
  ds''  <- concat <$> mapM (expandPatternBindings (qfv m ds' ++ qfv m e')) ds'
  return $ foldr (mkLet m) e' (scc bv (qfv m) ds'')

inlineVars :: [Decl] -> InlineEnv -> SIM InlineEnv
inlineVars ds env = case ds of
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
  | otherwise = Let [FreeDecl p vs'] e -- remove unused free variables
  where vs' = filter (`elem` qfv m e) vs
mkLet m [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] (Variable v')
  | v' == qualify v && v `notElem` qfv m e = e -- removed unused binding
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

-- Unfortunately, this transformation introduces a well-known space
-- leak (Wadler87:Leaks,Sparud93:Leaks) because the matched
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

-- Transform a pattern declaration @t = e@ into two declarations
-- @t = v, v = e@ whenever @t@ is not a variable. This is used to share
-- the expression @e@.
sharePatternRhs :: Decl -> SIM [Decl]
sharePatternRhs (PatternDecl p t rhs) = case t of
  VariablePattern _ -> return [PatternDecl p t rhs]
  _                 -> do
    ty <- monoType <$> getTypeOf t
    v  <- addRefId (srcRefOf p) <$> freshIdent patternId ty
    return [ PatternDecl p t                   (SimpleRhs p (mkVar v) [])
           , PatternDecl p (VariablePattern v) rhs
           ]
  where patternId n = mkIdent ("_#pat" ++ show n)
sharePatternRhs d                     = return [d]

-- fvs contains all variables used in the declarations and the body
-- of the let expression.
expandPatternBindings :: [Ident] -> Decl -> SIM [Decl]
expandPatternBindings fvs (PatternDecl p t (SimpleRhs p' e _)) = case t of
  VariablePattern _ -> return [PatternDecl p t (SimpleRhs p' e [])]
  _                 -> do
  pty   <- getTypeOf t            -- type of pattern
  mapM (mkSelectorDecl pty) vs
 where
  vs = filter (`elem` fvs) (bv t) -- used variables
  mkSelectorDecl pty v = do
    vty <- getTypeOf v
    f   <- freshIdent (updIdentName (++ '#' : idName v) . fpSelectorId)
                      (polyType (TypeArrow pty (identityType vty)))
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

getFunArity :: QualIdent -> SIM Int
getFunArity f = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  return (arrowArity (funType m tyEnv f))

funType :: ModuleIdent -> ValueEnv -> QualIdent -> Type
funType m tyEnv f = case qualLookupValue f tyEnv of
  [Value _ _ (ForAll _ ty)] -> ty
  _                         -> case qualLookupValue (qualQualify m f) tyEnv of
    [Value _ _ (ForAll _ ty)] -> ty
    _                         -> internalError $ "Simplify.funType " ++ show f

freshIdent :: (Int -> Ident) -> TypeScheme -> SIM Ident
freshIdent f ty@(ForAll _ t) = do
  m <- getModuleIdent
  x <- f <$> getNextId
  modifyValueEnv $ bindFun m x arity ty
  return x
  where arity = arrowArity t

mkVar :: Ident -> Expression
mkVar = Variable . qualify

varDecl :: Position -> Ident -> Expression -> Decl
varDecl p v e = PatternDecl p (VariablePattern v) (SimpleRhs p e [])

funDecl :: Position -> Ident -> [Pattern] -> Expression -> Decl
funDecl p f ts e = FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

identityType :: Type -> Type
identityType = TypeConstructor qIdentityId . return
  where qIdentityId = qualify (mkIdent "Identity")
