% -*- LaTeX -*-
% $Id: ILCompile.lhs,v 2.15 2004/04/30 01:55:08 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{ILCompile.lhs}
\section{Compiling the Intermediate Language}
This section describes a compiler that translates the intermediate
language into code for the Curry abstract machine. The compiler does
not perform any serious optimizations, yet.
\begin{verbatim}

> module ILCompile where
> import Ident
> import IL
> import qualified Cam
> import Env
> import List
> import Map
> import Maybe
> import Monad
> import SCC
> import Combined

> type CompState a = StateT [Cam.Name] Id a

> camCompile :: Module -> Cam.Module
> camCompile (Module m is ds) =
>   map compileImport is ++ concat (map compileDecl ds)
>   where compileImport = Cam.ImportDecl . Cam.mangle . moduleName

> camCompileData :: [Decl] -> [Cam.Decl]
> camCompileData ds = [compileData tc cs | DataDecl tc _ cs <- ds]

> compileDecl :: Decl -> [Cam.Decl]
> compileDecl (DataDecl tc _ cs) = [compileData tc cs]
> compileDecl (NewtypeDecl _ _ _) = []
> compileDecl (FunctionDecl f vs _ e) = [compileFun f vs e]
> compileDecl (ExternalDecl f cc ie ty) =
>   compileExt f cc (arity ty) (isIO ty) ie
>   where isIO (TypeConstructor tc tys) = tc == qIOId && length tys == 1
>         isIO (TypeVariable _) = False
>         isIO (TypeArrow _ ty) = isIO ty
>         arity (TypeArrow _ ty) = 1 + arity ty
>         arity _ = 0

> compileData :: QualIdent -> [ConstrDecl [Type]] -> Cam.Decl
> compileData tc cs = Cam.DataDecl (con tc) (map compileConstr cs)

> compileConstr :: ConstrDecl [Type] -> Cam.ConstrDecl
> compileConstr (ConstrDecl c tys)
>   | c == hidden = Cam.ConstrDecl hiddenCon 0
>   | otherwise = Cam.ConstrDecl (con c) (length tys)

> compileFun :: QualIdent -> [Ident] -> Expression -> Cam.Decl
> compileFun f vs e =
>   runSt (compile (Cam.FunctionDecl (fun f)) vs e) (nameSupply "_")
>   where compile = if isQSelectorId f then compileSelector else compileFunction
>         compileFunction f vs e =
>           liftM (f (map var vs) . unalias) (compileStrict [] e [])

\end{verbatim}
The code for external functions simply consists of a tail-call to the
entrypoint of the external code. In the case of \texttt{IO} functions,
the compiler has to generate two functions. The first of these returns
an I/O action and the other function is the I/O action itself.

The runtime system uses the usual state monad approach to implement
I/O actions but with a little optimization. The type \texttt{IO} can
be defined as
\begin{verbatim}
  type IO a = World -> (a,World)
\end{verbatim}
where \texttt{World} is a type representing the whole external world.
As the world is already present implicitly in the runtime system we do
not need an explicit representation for it. Instead, the runtime
system uses the constant \texttt{()} to represent the world. Because
this representation does not change, the runtime system actually uses
a simpler reader monad such that
\begin{verbatim}
  type IO a = () -> a
\end{verbatim}

\begin{verbatim}

> compileExt :: QualIdent -> CallConv -> Int -> Bool -> String -> [Cam.Decl]
> compileExt f cc n isIO fExt
>   | cc /= Primitive = error "only primitive calling convention supported yet"
>   | isIO = let vs = take (n + 1) (nameSupply "_") in
>            [ioFun f' f'_io vs,extFun f'_io vs]
>   | otherwise = [extFun f' (take n (nameSupply "_"))]
>   where f' = fun f
>         f'_io = Cam.mangleQualified (Cam.demangle f' ++ "/IO")
>         extFun f vs = Cam.FunctionDecl f vs (Cam.Exec (Cam.mangle fExt) vs)
>         ioFun f f_io (v:vs) =
>           Cam.FunctionDecl f vs
>             (Cam.Let [Cam.Bind v (Cam.Closure f_io vs)] (Cam.Return v))

\end{verbatim}
Special code has to be generated for the selector function that the
compiler introduces to avoid a space leak with pattern bindings (see
p.~\pageref{pattern-binding} in Sect.~\ref{sec:simplify}). The first
argument of the selector function is the pattern to be matched,
whereas the remaining arguments hold references to the other pattern
variables that have to be updated by the selector function. At the
beginning of the selector, these arguments are updated with queue-me
nodes in order to prevent concurrent threads from starting to evaluate
the corresponding selector functions and after the matching is
complete, they are updated with a pointer to the matched argument from
the pattern. The compiler uses the convention that the argument to be
updated uses the same name as the variable in the pattern. Note that
in the abstract machine code these variables have to use different
names. The function \texttt{compileSelector} takes care of inserting
the necessary \texttt{Lock} and \texttt{Update} instructions. It makes
use of the fact that the body of a selector is a nested case
expression whose innermost expression is a variable. We do not care
whether the selector functions are flexible or rigid.
\begin{verbatim}

> compileSelector :: ([Cam.Name] -> Cam.Stmt -> Cam.Decl)
>                 -> [Ident] -> Expression -> CompState Cam.Decl
> compileSelector f (v:vs) e =
>   do
>     vs' <- mapM (const freshName) vs
>     stmt <- compileSelectorExpr (zip vs vs') e
>     return (f (var v : vs') (foldr Cam.Lock stmt vs'))

> compileSelectorExpr :: [(Ident,Cam.Name)] -> Expression -> CompState Cam.Stmt
> compileSelectorExpr vs (Case ev (Variable v) [Alt t e]) =
>   do
>     v' <- freshName
>     stmt <- compileSelectorExpr vs e
>     return (Cam.Seq v' (Cam.Enter (var v)) $
>             Cam.Switch (rf ev) v' [caseTag noVar t stmt])
>   where noVar = internalError "invalid selector pattern"
> compileSelectorExpr vs (Variable v) =
>   return (foldr update (Cam.Enter (var v)) vs)
>   where update (v,v') = Cam.Update v' (var v)
> compileSelectorExpr _ _ = internalError "invalid selector function"

\end{verbatim}
The compilation of expressions is straight forward. Note that the
compiler can only handle constants, applications, and let bindings in
lazy positions. Case and non-deterministic or expressions have to be
lifted into global functions before compiling into abstract machine
code.
\begin{verbatim}

> compileStrict :: [Ident] -> Expression -> [Cam.Name] -> CompState Cam.Stmt
> compileStrict _ (Literal c) vs = returnWhnf (Literal c) vs
> compileStrict hnfs (Variable v) vs
>   | null vs =
>       return ((if v `elem` hnfs then Cam.Return else Cam.Enter) (var v))
>   | otherwise = return (Cam.Exec (apFun (length vs)) (var v:vs))
> compileStrict _ (Function f arity) vs
>   | n < arity = returnWhnf (Function f arity) vs
>   | otherwise = applyStrict (Cam.Exec (fun f) vs') vs''
>   where n = length vs
>         (vs',vs'') = splitAt arity vs
> compileStrict _ (Constructor c arity) vs =
>   returnWhnf (Constructor c arity) vs
> compileStrict hnfs (Apply e1 e2) vs =
>   do
>     v <- freshName
>     dss <- compileLazy v e2 []
>     st <- compileStrict hnfs e1 (v:vs)
>     return (foldr Cam.Let st dss)
> compileStrict hnfs (Case ev e cases) vs =
>   do
>     v <- freshName
>     stmt <- compileStrict hnfs e []
>     cases' <- mapM (flip (compileCase hnfs v) vs) cases
>     return (Cam.Seq v stmt $ Cam.Switch (rf ev) v cases')
> compileStrict hnfs (Or e1 e2) vs =
>   do
>     alts <- mapM (flip (compileStrict hnfs) vs) (branches e1 ++ branches e2)
>     return (Cam.Choices alts)
>   where branches (Or e1 e2) = branches e1 ++ branches e2
>         branches e = [e]
> compileStrict hnfs (Exist v e) vs =
>   do
>     st <- compileStrict (v:hnfs) e vs
>     return (Cam.Let [Cam.Bind (var v) Cam.Free] st)
> compileStrict hnfs (Let bd e2) vs =
>   do
>     dss <- compileBinding bd
>     st <- compileStrict (addHnfs [bd] hnfs) e2 vs
>     return (foldr Cam.Let st dss)
> compileStrict hnfs (Letrec bds e) vs =
>   do
>     dss <- compileRecBindings bds
>     st <- compileStrict (addHnfs bds hnfs) e vs
>     return (foldr Cam.Let st dss)

> returnWhnf :: Expression -> [Cam.Name] -> CompState Cam.Stmt
> returnWhnf e vs =
>   do
>     v <- freshName
>     dss <- compileLazy v e vs
>     return (foldr Cam.Let (Cam.Return v) dss)

> applyStrict :: Cam.Stmt -> [Cam.Name] -> CompState Cam.Stmt
> applyStrict st vs
>   | null vs = return st
>   | otherwise =
>       do
>         v' <- freshName
>         return (Cam.Seq v' st $ Cam.Exec (apFun (length vs)) (v':vs))

> literal :: Literal -> Cam.Literal
> literal (Char c) = Cam.Char c
> literal (Int i) = Cam.Int (fromInteger i)
> literal (Float f) = Cam.Float f

> addHnfs :: [Binding] -> [Ident] -> [Ident]
> addHnfs bds hnfs = [v | Binding v e <- bds, isHnf hnfs e] ++ hnfs

> isHnf :: [Ident] -> Expression -> Bool
> isHnf _ (Literal _) = True
> isHnf hnfs (Variable v) = v `elem` hnfs
> isHnf _ (Function _ n) = n > 0
> isHnf _ (Constructor _ _) = True
> isHnf _ (Apply e1 e2) = isHnfApp e1 [e2]
> isHnf hnfs (Exist v e) = isHnf (v:hnfs) e
> isHnf hnfs (Let bd e) = isHnf (addHnfs [bd] hnfs) e
> isHnf hnfs (Letrec bds e) = isHnf (addHnfs bds hnfs) e
> isHnf _ _ = internalError "isHnf"

> isHnfApp :: Expression -> [Expression] -> Bool
> isHnfApp (Variable  _) _ = False
> isHnfApp (Function _ n) es = n > length es
> isHnfApp (Constructor _ _) _ = True
> isHnfApp (Apply e1 e2) es = isHnfApp e1 (e2:es)
> isHnfApp (Exist _ e) es = isHnfApp e es
> isHnfApp (Let _ e) es = isHnfApp e es
> isHnfApp (Letrec _ e) es = isHnfApp e es
> isHnfApp _ _ = internalError "isHnfApp"

> rf :: Eval -> Cam.RF
> rf Rigid = Cam.Rigid
> rf Flex  = Cam.Flex

> compileCase :: [Ident] -> Cam.Name -> Alt -> [Cam.Name] -> CompState Cam.Case
> compileCase hnfs v (Alt t e) vs =
>   liftM (caseTag v t) (compileStrict hnfs e vs)

> caseTag :: Cam.Name -> ConstrTerm -> Cam.Stmt -> Cam.Case
> caseTag _ (LiteralPattern l) = Cam.Case (Cam.LitCase (literal l))
> caseTag _ (ConstructorPattern c vs) =
>   Cam.Case (Cam.ConstrCase (con c) (map var vs))
> caseTag v (VariablePattern v') =
>   Cam.Case Cam.DefaultCase . Cam.Let [Cam.Bind (var v') (Cam.Ref v)]

\end{verbatim}
When compiling an expression in lazy -- i.e., argument -- position,
the compiler returns a list of abstract machine code binding groups.
We generate minimal binding groups here in order to improve the
efficiency of the compiler.
\begin{verbatim}

> compileBinding :: Binding -> CompState [[Cam.Bind]]
> compileBinding (Binding v e) = compileLazy (var v) e []

> compileRecBindings :: [Binding] -> CompState [[Cam.Bind]]
> compileRecBindings =
>   liftM (scc bound free . concatMap concat) . mapM compileBinding
>   where bound (Cam.Bind v _) = [v]
>         free (Cam.Bind _ n) = vars n
>         vars (Cam.Lit _) = []
>         vars (Cam.Constr _ vs) = vs
>         vars (Cam.Closure _ vs) = vs
>         vars (Cam.Lazy _ vs) = vs
>         vars Cam.Free = []
>         vars (Cam.Ref v) = [v]

> compileLazy :: Cam.Name -> Expression -> [Cam.Name] -> CompState [[Cam.Bind]]
> compileLazy u (Literal l) vs
>   | null vs = bindVar u (Cam.Lit (literal l))
>   | otherwise = internalError "compileLazy(Literal): type error"
> compileLazy u (Variable v) vs
>   | null vs = bindVar u (Cam.Ref (var v))
>   | otherwise = bindVar u (Cam.Lazy (apFun (length vs)) (var v:vs))
> compileLazy u (Function f arity) vs
>   | n < arity = bindVar u (Cam.Closure (fun f) vs)
>   | n == arity = bindVar u (Cam.Lazy (fun f) vs)
>   | otherwise =
>       do
>         v <- freshName
>         dss <- bindVar v (Cam.Closure (fun f) vs')
>         dss' <- bindVar u (Cam.Lazy (apFun (n - arity)) (v:vs''))
>         return (dss ++ dss')
>   where n = length vs
>         (vs',vs'') = splitAt arity vs
> compileLazy u (Constructor c arity) vs
>   | n < arity = bindVar u (Cam.Closure (fun c) vs)
>   | n == arity = bindVar u (Cam.Constr (con c) vs)
>   | otherwise = internalError ("compileLazy(" ++ show c ++ "): type error")
>   where n = length vs
> compileLazy u (Apply e1 e2) vs =
>   do
>     v <- freshName
>     dss <- compileLazy v e2 []
>     dss' <- compileLazy u e1 (v:vs)
>     return (dss ++ dss')
> compileLazy u (Exist v e) vs =
>   do
>     dss <- compileLazy u e vs
>     return ([Cam.Bind (var v) Cam.Free] : dss)
> compileLazy u (Let bd e) vs =
>   do
>     dss <- compileBinding bd
>     dss' <- compileLazy u e vs
>     return (dss ++ dss')
> compileLazy u (Letrec bds e) vs =
>   do
>     dss <- compileRecBindings bds
>     dss' <- compileLazy u e vs
>     return (dss ++ dss')
> compileLazy _ e _ = internalError ("compileLazy: " ++ show e)

> bindVar :: Cam.Name -> Cam.Expr -> CompState [[Cam.Bind]]
> bindVar v n = return [[Cam.Bind v n]]

\end{verbatim}
In a postprocessing step, the generated code is optimized by removing
all \texttt{Ref} bindings from the code.
\begin{verbatim}

> unalias :: Cam.Stmt -> Cam.Stmt
> unalias = unaliasStmt zeroFM

> unaliasStmt :: FM Cam.Name Cam.Name -> Cam.Stmt -> Cam.Stmt
> unaliasStmt aliases (Cam.Return v) = Cam.Return (unaliasVar aliases v)
> unaliasStmt aliases (Cam.Enter v) = Cam.Enter (unaliasVar aliases v)
> unaliasStmt aliases (Cam.Exec f vs) =
>   Cam.Exec f (map (unaliasVar aliases) vs)
> unaliasStmt aliases (Cam.Lock v st) =
>   Cam.Lock (unaliasVar aliases v) (unaliasStmt aliases st)
> unaliasStmt aliases (Cam.Update v1 v2 st) =
>   Cam.Update (unaliasVar aliases v1) (unaliasVar aliases v2)
>              (unaliasStmt aliases st)
> unaliasStmt aliases (Cam.Seq v st1 st2) =
>   case unaliasStmt aliases st1 of
>     Cam.Return v' -> unaliasStmt (addToFM v v' aliases) st2
>     st1' -> Cam.Seq v st1' (unaliasStmt aliases st2)
> unaliasStmt aliases (Cam.Let bds st) =
>   mkLet [Cam.Bind v (unaliasExpr aliases' n) | Cam.Bind v n <- bds'']
>         (unaliasStmt aliases' st)
>   where (bds',bds'') = partition isAlias bds
>         aliases' = foldr (uncurry addToFM) aliases
>                          [(v,unaliasVar aliases' v')
>                          | Cam.Bind v (Cam.Ref v') <- bds']
>         mkLet bds = if null bds then id else Cam.Let bds
>         isAlias (Cam.Bind _ (Cam.Ref _)) = True
>         isAlias (Cam.Bind _ _) = False
> unaliasStmt aliases (Cam.Switch rf v cases) =
>   Cam.Switch rf (unaliasVar aliases v) (map (unaliasCase aliases) cases)
> unaliasStmt aliases (Cam.Choices alts) =
>   Cam.Choices (map (unaliasStmt aliases) alts)

> unaliasExpr :: FM Cam.Name Cam.Name -> Cam.Expr -> Cam.Expr
> unaliasExpr aliases (Cam.Lit c) = Cam.Lit c
> unaliasExpr aliases (Cam.Constr c vs) =
>   Cam.Constr c (map (unaliasVar aliases) vs)
> unaliasExpr aliases (Cam.Closure f vs) =
>   Cam.Closure f (map (unaliasVar aliases) vs)
> unaliasExpr aliases (Cam.Lazy f vs) =
>   Cam.Lazy f (map (unaliasVar aliases) vs)
> unaliasExpr aliases Cam.Free = Cam.Free

> unaliasCase :: FM Cam.Name Cam.Name -> Cam.Case -> Cam.Case
> unaliasCase aliases (Cam.Case t st) = Cam.Case t (unaliasStmt aliases st)

> unaliasVar :: FM Cam.Name Cam.Name -> Cam.Name -> Cam.Name
> unaliasVar aliases v = fromMaybe v (lookupFM v aliases)

\end{verbatim}
Variable, constructor, and function names have to be mangled into the
external representation used by the abstract machine code.
\begin{verbatim}

> var :: Ident -> Cam.Name
> var v = Cam.mangle (show v)

> fun :: QualIdent -> Cam.Name
> fun f = Cam.mangleQualified (show f)

> apFun :: Int -> Cam.Name
> apFun n = Cam.mangle ('@' : if n == 1 then "" else show n)

> con :: QualIdent -> Cam.Name
> con c = Cam.mangleQualified (show c)

> hiddenCon :: Cam.Name
> hiddenCon = Cam.Name "_"

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> hidden :: QualIdent
> hidden = qualify anonId

> nameSupply :: String -> [Cam.Name]
> nameSupply v = [Cam.Name (v ++ show i) | i <- [0..]]

> freshName :: CompState Cam.Name
> freshName = liftM head (updateSt tail)

> internalError :: String -> a
> internalError what = error ("internal error: " ++ what)

\end{verbatim}
