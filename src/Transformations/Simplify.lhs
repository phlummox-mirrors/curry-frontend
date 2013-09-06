% $Id: Simplify.lhs,v 1.10 2004/02/13 14:02:58 wlux Exp $
%
% Copyright (c) 2003, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{Simplify.lhs}
\section{Optimizing the Desugared Code}\label{sec:simplify}
After desugaring the source code, but before lifting local
declarations, the compiler performs a few simple optimizations to
improve the efficiency of the generated code. In addition, the
optimizer replaces pattern bindings with simple variable bindings and
selector functions.

Currently, the following optimizations are implemented:

\begin{itemize}
\item Remove unused declarations.
\item Inline simple constants.
\item Compute minimal binding groups.
\item Under certain conditions, inline local function definitions.
\end{itemize}
\begin{verbatim}

> module Transformations.Simplify (simplify) where

> import Control.Monad (liftM, liftM2)
> import Control.Monad.State as S (State, runState, gets, modify)
> import qualified Data.Map as Map (Map, empty, insert, lookup)

> import Curry.Base.Position
> import Curry.Base.Ident
> import Curry.Syntax

> import Base.Expr
> import Base.Messages (internalError)
> import Base.SCC
> import Base.Types
> import Base.Typing
> import Base.Utils (concatMapM)

> import Env.Value (ValueEnv, ValueInfo (..), bindFun, qualLookupValue)

> data SimplifyState = SimplifyState
>   { moduleIdent :: ModuleIdent -- read-only!
>   , valueEnv    :: ValueEnv
>   , nextId      :: Int         -- counter
>   , flat        :: Bool        -- read-only!
>   }

> type SIM = S.State SimplifyState
> type InlineEnv = Map.Map Ident Expression

> getModuleIdent :: SIM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> getNextId :: SIM Int
> getNextId = do
>   nid <- S.gets nextId
>   S.modify $ \s -> s { nextId = succ nid }
>   return nid

> modifyValueEnv :: (ValueEnv -> ValueEnv) -> SIM ()
> modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

> getValueEnv :: SIM ValueEnv
> getValueEnv = S.gets valueEnv

> isFlat :: SIM Bool
> isFlat = S.gets flat

> simplify :: Bool -> ValueEnv ->Module -> (Module, ValueEnv)
> simplify flags tyEnv mdl@(Module _ m _ _ _) = (mdl', valueEnv s')
>   where (mdl', s') = S.runState (simModule mdl)
>                                 (SimplifyState m tyEnv 1 flags)

> simModule :: Module -> SIM (Module)
> simModule (Module ps m es is ds)
>   = Module ps m es is `liftM` mapM (simDecl Map.empty) ds

> simDecl :: InlineEnv -> Decl -> SIM Decl
> simDecl env (FunctionDecl p f eqs) =
>   FunctionDecl p f `liftM` concatMapM (simEquation env) eqs
> simDecl env (PatternDecl  p t rhs) =
>   PatternDecl p t  `liftM` simRhs env rhs
> simDecl _   d                      = return d

\end{verbatim}
After simplifying the right hand side of an equation, the compiler
transforms declarations of the form
\begin{quote}\tt
  $f\;t_1\dots t_{k-k'}\;x_{k-k'+1}\dots x_{k}$ =
    let $f'\;t'_1\dots t'_{k'}$ = $e$ in
    $f'\;x_1\dots x_{k'}$
\end{quote}
into the equivalent definition
\begin{quote}\tt
  $f\;t_1\dots t_{k-k'}\;(x_{k-k'+1}$@$t'_1)\dots(x_k$@$t'_{k'})$ = $e$
\end{quote}
where the arities of $f$ and $f'$ are $k$ and $k'$, respectively, and
$x_{k-k'+1},\dots,x_{k}$ are variables. This optimization was
introduced in order to avoid an auxiliary function being generated for
definitions whose right-hand side is a $\lambda$-expression, e.g.,
\verb|f . g = \x -> f (g x)|. This declaration is transformed into
\verb|(.) f g x = let lambda x = f (g x) in lambda x| by desugaring
and in turn is optimized into \verb|(.) f g x = f (g x)|, here. The
transformation can obviously be generalized to the case where $f'$ is
defined by more than one equation. However, we must be careful not to
change the evaluation mode of arguments. Therefore, the transformation
is applied only if $f$ and $f'$ use them same evaluation mode or all
of the arguments $t'_1,\dots,t'_k$ are variables. Actually, the
transformation could be applied to the case where the arguments
$t_1,\dots,t_{k-k'}$ are all variables as well, but in this case the
evaluation mode of $f$ may have to be changed to match that of $f'$.

We have to be careful with this optimization in conjunction with
newtype constructors. It is possible that the local function is
applied only partially, e.g., for
\begin{verbatim}
  newtype ST s a = ST (s -> (a,s))
  returnST x = ST (\s -> (x,s))
\end{verbatim}
the desugared code is equivalent to
\begin{verbatim}
  returnST x = let lambda1 s = (x,s) in lambda1
\end{verbatim}
We must not ``optimize'' this into \texttt{returnST x s = (x,s)}
because the compiler assumes that \texttt{returnST} is a unary
function.

Note that this transformation is not strictly semantic preserving as
the evaluation order of arguments can be changed. This happens if $f$
is defined by more than one rule with overlapping patterns and the
local functions of each rule have disjoint patterns. As an example,
consider the function
\begin{verbatim}
  f (Just x) _ = let g (Left z)  = x + z in g
  f _ (Just y) = let h (Right z) = y + z in h
\end{verbatim}
The definition of \texttt{f} is non-deterministic because of the
overlapping patterns in the first and second argument. However, the
optimized definition
\begin{verbatim}
  f (Just x) _ (Left z)  = x + z
  f _ (Just y) (Right z) = y + z
\end{verbatim}
is deterministic. It will evaluate and match the third argument first,
whereas the original definition is going to evaluate the first or the
second argument first, depending on the non-deterministic branch
chosen. As such definitions are presumably rare, and the optimization
avoids a non-deterministic split of the computation, we put up with
the change of evaluation order.

This transformation is actually just a special case of inlining a
(local) function definition. We are unable to handle the general case
because it would require to represent the pattern matching code
explicitly in a Curry expression.
\begin{verbatim}

> simEquation :: InlineEnv -> Equation -> SIM [Equation]
> simEquation env (Equation p lhs rhs) = do
>   m     <- getModuleIdent
>   rhs'  <- simRhs env rhs
>   tyEnv <- getValueEnv
>   return $ inlineFun m tyEnv p lhs rhs'

> inlineFun :: ModuleIdent -> ValueEnv -> Position -> Lhs -> Rhs -> [Equation]
> inlineFun m tyEnv p (FunLhs f ts)
>           (SimpleRhs _ (Let [FunctionDecl _ f' eqs'] e) _)
>   | True -- False -- inlining of functions is deactivated (hsi)
>    && f' `notElem` qfv m eqs' && e' == Variable (qualify f') &&
>     n == arrowArity (funType m tyEnv (qualify f')) &&
>      and [all isVarPattern ts1 | Equation _ (FunLhs _ ts1) _ <- eqs'] =
>     map (mergeEqns p f ts' vs') eqs'
>   where n :: Int                      -- type signature necessary for nhc
>         (n,vs',ts',e') = etaReduce 0 [] (reverse ts) e
>         mergeEqns p1 f1 ts1 vs (Equation _ (FunLhs _ ts2) rhs) =
>           Equation p1 (FunLhs f1 (ts1 ++ zipWith AsPattern vs ts2)) rhs
>         mergeEqns _ _ _ _ _ = error "Simplify.inlineFun.mergeEqns: no pattern match"
>         etaReduce n1 vs (VariablePattern v : ts1) (Apply e1 (Variable v'))
>           | qualify v == v' = etaReduce (n1+1) (v:vs) ts1 e1
>         etaReduce n1 vs ts1 e1 = (n1,vs,reverse ts1,e1)
> inlineFun _ _ p lhs rhs = [Equation p lhs rhs]

> simRhs :: InlineEnv -> Rhs -> SIM Rhs
> simRhs env (SimpleRhs p e _) =
>   (\ e' -> SimpleRhs p e' []) `liftM` simExpr env e
> simRhs _   (GuardedRhs  _ _) = error "Simplify.simRhs: guarded rhs"

\end{verbatim}
Variables that are bound to (simple) constants and aliases to other
variables are substituted. In terms of conventional compiler
technology these optimizations correspond to constant folding and copy
propagation, respectively. The transformation is applied recursively
to a substituted variable in order to handle chains of variable
definitions.

The bindings of a let expression are sorted topologically in
order to split them into minimal binding groups. In addition,
local declarations occurring on the right hand side of a pattern
declaration are lifted into the enclosing binding group using the
equivalence (modulo $\alpha$-conversion) of \texttt{let}
$x$~=~\texttt{let} \emph{decls} \texttt{in} $e_1$ \texttt{in} $e_2$
and \texttt{let} \emph{decls}\texttt{;} $x$~=~$e_1$ \texttt{in} $e_2$.
This transformation avoids the creation of some redundant lifted
functions in later phases of the compiler.
\begin{verbatim}

> simExpr :: InlineEnv -> Expression -> SIM Expression
> simExpr _   l@(Literal     _) = return l
> simExpr env v@(Variable    x)
>   | isQualified x = return v
>   | otherwise     = maybe (return v) (simExpr env)
>                           (Map.lookup (unqualify x) env)
> simExpr _   c@(Constructor _) = return c
> simExpr env (Apply (Let ds e1) e2) = simExpr env (Let ds (Apply e1 e2))
> simExpr env (Apply (Case r ct e1 alts) e2)
>   = simExpr env (Case r ct e1 (map (applyToAlt e2) alts))
>   where applyToAlt e (Alt p t rhs) = Alt p t (applyRhs rhs e)
>         applyRhs (SimpleRhs p e1' _) e2' = SimpleRhs p (Apply e1' e2') []
>         applyRhs (GuardedRhs _ _) _ = error "Simplify.simExpr.applyRhs: Guarded rhs"
> simExpr env (Apply e1 e2) = liftM2 Apply (simExpr env e1) (simExpr env e2)
> simExpr env (Let ds e) = do
>     m <- getModuleIdent
>     tyEnv <- getValueEnv
>     dss' <- mapM (sharePatternRhs tyEnv) ds
>     simplifyLet env (scc bv (qfv m) (foldr hoistDecls [] (concat dss'))) e
> simExpr env (Case r ct e alts) =
>   liftM2 (Case r ct) (simExpr env e) (mapM (simplifyAlt env) alts)
> simExpr env (Typed e ty) = flip Typed ty `liftM` simExpr env e
> simExpr _ _ = error "Simplify.simExpr: no pattern match"

> simplifyAlt :: InlineEnv -> Alt -> SIM Alt
> simplifyAlt env (Alt p t rhs) = Alt p t `liftM` simRhs env rhs

> hoistDecls :: Decl -> [Decl] -> [Decl]
> hoistDecls (PatternDecl p t (SimpleRhs p' (Let ds e) _)) ds'
>  = foldr hoistDecls ds' (PatternDecl p t (SimpleRhs p' e []) : ds)
> hoistDecls d ds = d : ds

\end{verbatim}
The declaration groups of a let expression are first processed from
outside to inside, simplifying the right hand sides and collecting
inlineable expressions on the fly. At present, only simple constants
and aliases to other variables are inlined. A constant is considered
simple if it is either a literal, a constructor, or a non-nullary
function. Note that it is not possible to define nullary functions in
local declarations in Curry. Thus, an unqualified name always refers
to either a variable or a non-nullary function.  Applications of
constructors and partial applications of functions to at least one
argument are not inlined because the compiler has to allocate space
for them, anyway. In order to prevent non-termination, recursive
binding groups are not processed.

With the list of inlineable expressions, the body of the let is
simplified and then the declaration groups are processed from inside
to outside to construct the simplified, nested let expression. In
doing so unused bindings are discarded. In addition, all pattern
bindings are replaced by simple variable declarations using selector
functions to access the pattern variables.
\begin{verbatim}

> simplifyLet :: InlineEnv -> [[Decl]] -> Expression -> SIM Expression
> simplifyLet env []       e = simExpr env e
> simplifyLet env (ds:dss) e = do
>   m <- getModuleIdent
>   ds' <- mapM (simDecl env) ds
>   tyEnv <- getValueEnv
>   e' <- simplifyLet (inlineVars m tyEnv ds' env) dss e
>   dss'' <- mapM (expandPatternBindings tyEnv (qfv m ds' ++ qfv m e')) ds'
>   return (foldr (mkLet m) e' (scc bv (qfv m) (concat dss'')))

> inlineVars :: ModuleIdent -> ValueEnv -> [Decl] -> InlineEnv -> InlineEnv
> inlineVars m tyEnv [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] env
>   | canInline e = Map.insert v e env
>   where
>   canInline (Literal     _) = True
>   canInline (Constructor _) = True
>   -- inlining of variables is deactivated (hsi) -- TODO (bjp, 2012-01-03)
>   canInline (Variable v')
>     | isQualified v' = arrowArity (funType m tyEnv v') > 0
>     | otherwise = v /= unqualify v'
>   canInline _               = False
> inlineVars _ _ _ env = env

> mkLet :: ModuleIdent -> [Decl] -> Expression -> Expression
> mkLet m [FreeDecl p vs] e
>   | null vs'  = e
>   | otherwise = Let [FreeDecl p vs'] e
>   where vs' = filter (`elem` qfv m e) vs
> mkLet m [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] (Variable v')
>   | v' == qualify v && v `notElem` qfv m e = e
> mkLet m ds e
>   | null (filter (`elem` qfv m e) (bv ds)) = e
>   | otherwise = Let ds e

\end{verbatim}
\label{pattern-binding}
In order to implement lazy pattern matching in local declarations,
pattern declarations $t$~\texttt{=}~$e$ where $t$ is not a variable
are transformed into a list of declarations
$v_0$~\texttt{=}~$e$\texttt{;} $v_1$~\texttt{=}~$f_1$~$v_0$\texttt{;}
\dots{} $v_n$~\texttt{=}~$f_n$~$v_0$ where $v_0$ is a fresh variable,
$v_1,\dots,v_n$ are the variables occurring in $t$ and the auxiliary
functions $f_i$ are defined by $f_i$~$t$~\texttt{=}~$v_i$ (see also
appendix D.8 of the Curry report~\cite{Hanus:Report}). The bindings
$v_0$~\texttt{=}~$e$ are introduced before splitting the declaration
groups of the enclosing let expression (cf. the \texttt{Let} case in
\texttt{simExpr} above) so that they are placed in their own
declaration group whenever possible. In particular, this ensures that
the new binding is discarded when the expression $e$ is itself a
variable.

Unfortunately, this transformation introduces a well-known space
leak~\cite{Wadler87:Leaks,Sparud93:Leaks} because the matched
expression cannot be garbage collected until all of the matched
variables have been evaluated. Consider the following function:
\begin{verbatim}
  f x | all (' ' ==) cs = c where (c:cs) = x
\end{verbatim}
One might expect the call \verb|f (replicate 10000 ' ')| to execute in
constant space because (the tail of) the long list of blanks is
consumed and discarded immediately by \texttt{all}. However, the
application of the selector function that extracts the head of the
list is not evaluated until after the guard has succeeded and thus
prevents the list from being garbage collected.

In order to avoid this space leak we use the approach
from~\cite{Sparud93:Leaks} and update all pattern variables when one
of the selector functions has been evaluated. Therefore all pattern
variables except for the matched one are passed as additional
arguments to each of the selector functions. Thus, each of these
variables occurs twice in the argument list of a selector function,
once in the first argument and also as one of the remaining arguments.
This duplication of names is used by the compiler to insert the code
that updates the variables when generating abstract machine code.

By its very nature, this transformation introduces cyclic variable
bindings. Since cyclic bindings are not supported by PAKCS, we revert
to a simpler translation when generating FlatCurry output.

We will add only those pattern variables as additional arguments which
are actually used in the code. This reduces the number of auxiliary
variables and can prevent the introduction of a recursive binding
group when only a single variable is used. It is also the reason for
performing this transformation here instead of in the \texttt{Desugar}
module. The selector functions are defined in a local declaration on
the right hand side of a projection declaration so that there is
exactly one declaration for each used variable.

Another problem of the translation scheme is the handling of pattern
variables with higher-order types, e.g.,
\begin{verbatim}
  strange :: [a->a] -> Maybe (a->a)
  strange xs = Just x
    where (x:_) = xs
\end{verbatim}
By reusing the types of the pattern variables, the selector function
\verb|f (x:_) = x| has type \texttt{[a->a] -> a -> a} and therefore
seems to be binary function. Thus, in the goal \verb|strange []| the
selector is only applied partially and not evaluated. Note that this
goal will fail without the type annotation. In order to ensure that a
selector function is always evaluated when the corresponding variable
is used, we assume that the projection declarations -- ignoring the
additional arguments to prevent the space leak -- are actually defined
by $f_i$~$t$~\texttt{= I}~$v_i$, using a private renaming type
\begin{verbatim}
  newtype Identity a = I a
\end{verbatim}
As newtype constructors are completely transparent to the compiler,
this does not change the generated code, but only the types of the
selector functions.
\begin{verbatim}

> sharePatternRhs :: ValueEnv -> Decl -> SIM [Decl]
> sharePatternRhs tyEnv (PatternDecl p t rhs) = case t of
>   VariablePattern _ -> return [PatternDecl p t rhs]
>   _ -> do
>     v0 <- freshIdent patternId (monoType (typeOf tyEnv t))
>     let v = addRefId (srcRefOf p) v0
>     return [ PatternDecl p t (SimpleRhs p (mkVar v) [])
>            , PatternDecl p (VariablePattern v) rhs
>            ]
>   where patternId n = mkIdent ("_#pat" ++ show n)
> sharePatternRhs _ d = return [d]

> expandPatternBindings :: ValueEnv -> [Ident] -> Decl -> SIM [Decl]
> expandPatternBindings tyEnv fvs (PatternDecl p t (SimpleRhs p' e _)) = do
>   flags <- isFlat
>   case t of
>     VariablePattern _ -> return [PatternDecl p t (SimpleRhs p' e [])]
>     _
>       | flags -> do
>           fs <- sequence (zipWith getId tys vs)
>           return (zipWith (flatProjectionDecl p t e) fs vs)
>       | otherwise -> do
>           fs <- mapM (freshIdent fpSelectorId . selectorType ty) (shuffle tys)
>           return (zipWith (projectionDecl p t e) fs (shuffle vs))
>   where
>   vs  = filter (`elem` fvs) (bv t)
>   ty  = typeOf tyEnv t
>   tys = map (typeOf tyEnv) vs
>
>   getId t1 v = freshIdent (\ i -> updIdentName (++ '#' : idName v) (fpSelectorId i))
>                            (flatSelectorType ty t1)
>   flatSelectorType ty0 ty1          = polyType (TypeArrow ty0 (identityType ty1))
>   flatSelectorDecl p1 f1 t1 v1      = funDecl p1 f1 [t1] (mkVar v1)
>   flatProjectionDecl p1 t1 e1 f1 v1 = varDecl p1 v1 (Let [flatSelectorDecl p1 f1 t1 v1] (Apply (mkVar f1) e1))
>
>   selectorType ty0 (ty1:tys1) = polyType (foldr TypeArrow (identityType ty1) (ty0:tys1))
>   selectorType _   []         = error "Simplify.expandPatternBindings.selectorType: empty list"
>
>   selectorDecl p1 f t1 (v:vs1) = funDecl p1 f (t1 : map VariablePattern vs1) (mkVar v)
>   selectorDecl _  _ _  []      = error "Simplify.expandPatternBindings.selectorDecl: empty list"
>
>   projectionDecl p1 t1 e1 f (v:vs1) = varDecl p1 v $
>     Let [selectorDecl p1 f t1 (v:vs1)] (foldl applyVar (Apply (mkVar f) e1) vs1)
>   projectionDecl _ _ _ _ [] = error "Simplify.expandPatternBindings.projectionDecl: empty list"
>
> expandPatternBindings _ _ d = return [d]

\end{verbatim}
Auxiliary functions
\begin{verbatim}

> isVarPattern :: Pattern -> Bool
> isVarPattern (VariablePattern      _) = True
> isVarPattern (AsPattern          _ t) = isVarPattern t
> isVarPattern (ConstructorPattern _ _) = False
> isVarPattern (LiteralPattern       _) = False
> isVarPattern _ = error "Simplify.isVarPattern: no pattern match"

> funType :: ModuleIdent -> ValueEnv -> QualIdent -> Type
> funType m tyEnv f = case qualLookupValue f tyEnv of
>   [Value _ _ (ForAll _ ty)] -> ty
>   _ -> case qualLookupValue (qualQualify m f) tyEnv of
>     [Value _ _ (ForAll _ ty)] -> ty
>     _ -> internalError $ "Simplify.funType " ++ show f

> freshIdent :: (Int -> Ident) -> TypeScheme -> SIM Ident
> freshIdent f ty@(ForAll _ t) = do
>   m <- getModuleIdent
>   x <- f `liftM` getNextId
>   modifyValueEnv $ bindFun m x arity ty
>   return x
>   where arity = arrowArity t

> shuffle :: [a] -> [[a]]
> shuffle xs = shuffle' id xs
>   where shuffle' _ []       = []
>         shuffle' f (x1:xs1) = (x1 : f xs1) : shuffle' (f . (x1:)) xs1

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

> applyVar :: Expression -> Ident -> Expression
> applyVar e v = Apply e (mkVar v)

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p v e = PatternDecl p (VariablePattern v) (SimpleRhs p e [])

> funDecl :: Position -> Ident -> [Pattern] -> Expression -> Decl
> funDecl p f ts e = FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> identityType :: Type -> Type
> identityType = TypeConstructor qIdentityId . return
>   where qIdentityId = qualify (mkIdent "Identity")

\end{verbatim}
