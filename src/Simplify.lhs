% -*- LaTeX -*-
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

> module Simplify(simplify) where
> import Base
> import Combined
> import Env
> import Monad
> import SCC
> import Typing

> type SimplifyState a = StateT ValueEnv (ReaderT EvalEnv (StateT Int Id)) a
> type InlineEnv = Env Ident Expression

> simplify :: Bool -> ValueEnv -> EvalEnv -> Module -> (Module,ValueEnv)
> simplify flat tyEnv evEnv m =
>   runSt (callRt (callSt (simplifyModule flat m) tyEnv) evEnv) 1

> simplifyModule :: Bool -> Module -> SimplifyState (Module,ValueEnv)
> simplifyModule flat (Module m es ds) =
>   do
>     ds' <- mapM (simplifyDecl flat m emptyEnv) ds
>     tyEnv <- fetchSt
>     return (Module m es ds',tyEnv)

> simplifyDecl :: Bool -> ModuleIdent -> InlineEnv -> Decl -> SimplifyState Decl
> simplifyDecl flat m env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f . concat) (mapM (simplifyEquation flat m env) eqs)
> simplifyDecl flat m env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (simplifyRhs flat m env rhs)
> simplifyDecl _ _ _ d = return d

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

> simplifyEquation :: Bool -> ModuleIdent -> InlineEnv -> Equation
>                  -> SimplifyState [Equation]
> simplifyEquation flat m env (Equation p lhs rhs) =
>   do
>     rhs' <- simplifyRhs flat m env rhs
>     tyEnv <- fetchSt
>     evEnv <- liftSt envRt
>     return (inlineFun m tyEnv evEnv p lhs rhs')

> inlineFun :: ModuleIdent -> ValueEnv -> EvalEnv -> Position -> Lhs -> Rhs
>           -> [Equation]
> inlineFun m tyEnv evEnv p (FunLhs f ts)
>           (SimpleRhs _ (Let [FunctionDecl _ f' eqs'] e) _)
>   | f' `notElem` qfv m eqs' && e' == Variable (qualify f') &&
>     n == arrowArity (funType m tyEnv (qualify f')) &&
>     (evMode evEnv f == evMode evEnv f' ||
>      and [all isVarPattern ts | Equation _ (FunLhs _ ts) _ <- eqs']) =
>     map (merge p f ts' vs') eqs'
>   where n :: Int                      -- type signature necessary for nhc
>         (n,vs',ts',e') = etaReduce 0 [] (reverse ts) e
>         merge p f ts vs (Equation _ (FunLhs _ ts') rhs) =
>           Equation p (FunLhs f (ts ++ zipWith AsPattern vs ts')) rhs
>         etaReduce n vs (VariablePattern v : ts) (Apply e (Variable v'))
>           | qualify v == v' = etaReduce (n+1) (v:vs) ts e
>         etaReduce n vs ts e = (n,vs,reverse ts,e)
> inlineFun _ _ _ p lhs rhs = [Equation p lhs rhs]

> simplifyRhs :: Bool -> ModuleIdent -> InlineEnv -> Rhs -> SimplifyState Rhs
> simplifyRhs flat m env (SimpleRhs p e _) =
>   do
>     e' <- simplifyExpr flat m env e
>     return (SimpleRhs p e' [])

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

> simplifyExpr :: Bool -> ModuleIdent -> InlineEnv -> Expression
>              -> SimplifyState Expression
> simplifyExpr _ _ _ (Literal l) = return (Literal l)
> simplifyExpr flat m env (Variable v)
>   | isQualified v = return (Variable v)
>   | otherwise = maybe (return (Variable v)) (simplifyExpr flat m env)
>                       (lookupEnv (unqualify v) env)
> simplifyExpr _ _ _ (Constructor c) = return (Constructor c)
> simplifyExpr flat m env (Apply (Let ds e1) e2) =
>   simplifyExpr flat m env (Let ds (Apply e1 e2))
> simplifyExpr flat m env (Apply (Case e1 alts) e2) =
>   simplifyExpr flat m env (Case e1 (map (applyToAlt e2) alts))
>   where applyToAlt e (Alt p t rhs) = Alt p t (applyRhs rhs e)
>         applyRhs (SimpleRhs p e1 _) e2 = SimpleRhs p (Apply e1 e2) []
> simplifyExpr flat m env (Apply e1 e2) =
>   do
>     e1' <- simplifyExpr flat m env e1
>     e2' <- simplifyExpr flat m env e2
>     return (Apply e1' e2')
> simplifyExpr flat m env (Let ds e) =
>   do
>     tyEnv <- fetchSt
>     dss' <- mapM (sharePatternRhs m tyEnv) ds
>     simplifyLet flat m env
>                 (scc bv (qfv m) (foldr hoistDecls [] (concat dss'))) e
> simplifyExpr flat m env (Case e alts) =
>   do
>     e' <- simplifyExpr flat m env e
>     alts' <- mapM (simplifyAlt flat m env) alts
>     return (Case e' alts')

> simplifyAlt :: Bool -> ModuleIdent -> InlineEnv -> Alt -> SimplifyState Alt
> simplifyAlt flat m env (Alt p t rhs) =
>   liftM (Alt p t) (simplifyRhs flat m env rhs)

> hoistDecls :: Decl -> [Decl] -> [Decl]
> hoistDecls (PatternDecl p t (SimpleRhs p' (Let ds e) _)) ds' =
>   foldr hoistDecls ds' (PatternDecl p t (SimpleRhs p' e []) : ds)
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

> simplifyLet :: Bool -> ModuleIdent -> InlineEnv -> [[Decl]] -> Expression
>             -> SimplifyState Expression
> simplifyLet flat m env [] e = simplifyExpr flat m env e
> simplifyLet flat m env (ds:dss) e =
>   do
>     ds' <- mapM (simplifyDecl flat m env) ds
>     tyEnv <- fetchSt
>     e' <- simplifyLet flat m (inlineVars m tyEnv ds' env) dss e
>     dss'' <-
>       mapM (expandPatternBindings flat m tyEnv (qfv m ds' ++ qfv m e')) ds'
>     return (foldr (mkLet m) e' (scc bv (qfv m) (concat dss'')))

> inlineVars :: ModuleIdent -> ValueEnv -> [Decl] -> InlineEnv -> InlineEnv
> inlineVars m tyEnv [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] env
>   | canInline e = bindEnv v e env
>   where canInline (Literal _) = True
>         canInline (Constructor _) = True
>         canInline (Variable v')
>           | isQualified v' = arrowArity (funType m tyEnv v') > 0
>           | otherwise = v /= unqualify v'
>         canInline _ = False
> inlineVars _ _ _ env = env

> mkLet :: ModuleIdent -> [Decl] -> Expression -> Expression
> mkLet m [ExtraVariables p vs] e
>   | null vs' = e
>   | otherwise = Let [ExtraVariables p vs'] e
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
\texttt{simplifyExpr} above) so that they are placed in their own
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

> sharePatternRhs :: ModuleIdent -> ValueEnv -> Decl -> SimplifyState [Decl]
> sharePatternRhs m tyEnv (PatternDecl p t rhs) =
>   case t of
>     VariablePattern _ -> return [PatternDecl p t rhs]
>     _ -> 
>       do
>         v <- freshIdent m patternId (monoType (typeOf tyEnv t))
>         return [PatternDecl p t (SimpleRhs p (mkVar v) []),
>                 PatternDecl p (VariablePattern v) rhs]
>   where patternId n = mkIdent ("_#pat" ++ show n)
> sharePatternRhs _ _ d = return [d]

> expandPatternBindings :: Bool -> ModuleIdent -> ValueEnv -> [Ident] -> Decl
>                       -> SimplifyState [Decl]
> expandPatternBindings flat m tyEnv fvs (PatternDecl p t (SimpleRhs p' e _)) =
>   case t of
>     VariablePattern _ -> return [PatternDecl p t (SimpleRhs p' e [])]
>     _
>       | flat ->
>           do
>             fs <- mapM (freshIdent m selectorId . flatSelectorType ty) tys
>             return (zipWith (flatProjectionDecl p t e) fs vs)
>       | otherwise ->
>           do
>             fs <- mapM (freshIdent m selectorId . selectorType ty)
>                        (shuffle tys)
>             return (zipWith (projectionDecl p t e) fs (shuffle vs))
>       where vs = filter (`elem` fvs) (bv t)
>             ty = typeOf tyEnv t
>             tys = map (typeOf tyEnv) vs
>             selectorType ty0 (ty:tys) =
>               polyType (foldr TypeArrow (identityType ty) (ty0:tys))
>             selectorDecl p f t (v:vs) =
>               funDecl p f (t:map VariablePattern vs) (mkVar v)
>             projectionDecl p t e f (v:vs) =
>               varDecl p v (Let [selectorDecl p f t (v:vs)]
>                                (foldl applyVar (Apply (mkVar f) e) vs))
>             flatSelectorType ty0 ty =
>               polyType (TypeArrow ty0 (identityType ty))
>             flatSelectorDecl p f t v = funDecl p f [t] (mkVar v)
>             flatProjectionDecl p t e f v =
>               varDecl p v (Let [flatSelectorDecl p f t v] (Apply (mkVar f) e))
> expandPatternBindings _ _ _ _ d = return [d]

\end{verbatim}
Auxiliary functions
\begin{verbatim}

> isVarPattern :: ConstrTerm -> Bool
> isVarPattern (VariablePattern _) = True
> isVarPattern (AsPattern _ t) = isVarPattern t
> isVarPattern (ConstructorPattern _ _) = False
> isVarPattern (LiteralPattern _) = False

> funType :: ModuleIdent -> ValueEnv -> QualIdent -> Type
> funType m tyEnv f =
>   case (qualLookupValue f tyEnv) of
>     [Value _ (ForAll _ ty)] -> ty
>     vs -> case (qualLookupValue (qualQualify m f) tyEnv) of
>             [Value _ (ForAll _ ty)] -> ty
>             _ -> internalError ("funType " ++ show f)

> evMode :: EvalEnv -> Ident -> Maybe EvalAnnotation
> evMode evEnv f = lookupEnv f evEnv

> freshIdent :: ModuleIdent -> (Int -> Ident) -> TypeScheme
>            -> SimplifyState Ident
> freshIdent m f ty =
>   do
>     x <- liftM f (liftSt (liftRt (updateSt (1 +))))
>     updateSt_ (bindFun m x ty)
>     return x

> shuffle :: [a] -> [[a]]
> shuffle xs = shuffle id xs
>   where shuffle _ [] = []
>         shuffle f (x:xs) = (x : f xs) : shuffle (f . (x:)) xs

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

> applyVar :: Expression -> Ident -> Expression
> applyVar e v = Apply e (mkVar v)

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p v e = PatternDecl p (VariablePattern v) (SimpleRhs p e [])

> funDecl :: Position -> Ident -> [ConstrTerm] -> Expression -> Decl
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> identityType :: Type -> Type
> identityType = TypeConstructor qIdentityId . return
>   where qIdentityId = qualify (mkIdent "Identity")

\end{verbatim}
