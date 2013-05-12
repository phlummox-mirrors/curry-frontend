% $Id: Desugar.lhs,v 1.42 2004/02/15 22:10:32 wlux Exp $
%
% Copyright (c) 2001-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}
The desugaring pass removes all syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item All function definitions are $\eta$-expanded.\\
  {\em Note:} Since this version is used as a frontend for PAKCS, the
  $\eta$-expansion had been disabled.

\item No guarded right hand sides occur in equations, pattern
  declarations, and case alternatives. In addition, the declaration
  lists of the right hand sides are empty; local declarations are
  transformed into let expressions.

\item Patterns in equations and case alternatives are composed only of
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructor applications, and
  \item as patterns.
  \end{itemize}

\item Expressions are composed only of
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructors,
  \item (binary) applications,
  \item let expressions, and
  \item case expressions.
  \end{itemize}

\item Applications $N\:x$ in patterns and expressions, where $N$ is a
  newtype constructor, are replaced by a $x$. Note that neither the
  newtype declaration itself nor partial applications of newtype
  constructors are changed.\footnote{It were possible to replace
  partial applications of newtype constructor by \texttt{prelude.id}.
  However, our solution yields a more accurate output when the result
  of a computation includes partial applications.}

\item Function patterns are replaced by variables and are integrated
  in a guarded right hand side using the \texttt{=:<=} operator

\item Records, which currently must be declared using the keyword
  \texttt{type}, are transformed into data types with one constructor.
  Record construction and pattern matching are represented using the
  record constructor. Selection and update are represented using selector
  and update functions which are generated for each record declaration.
  The record constructor must be entered into the type environment as well
  as the selector functions and the update functions.
\end{itemize}

\ToDo{Use a different representation for the restricted code instead
of using the syntax tree from \texttt{CurrySyntax}.}

\textbf{As we are going to insert references to real prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Transformations.Desugar (desugar) where

> import           Control.Arrow              (first, second)
> import           Control.Monad              (liftM, liftM2, liftM3, mplus)
> import qualified Control.Monad.State as S   (State, runState, gets, modify)
> import           Data.List                  ((\\), nub, tails)
> import           Data.Maybe                 (fromMaybe)
> import qualified Data.Set            as Set (Set, empty, member, insert)

> import Curry.Base.Ident
> import Curry.Base.Position hiding (first)
> import Curry.Syntax

> import Base.Expr
> import Base.CurryTypes (fromType)
> import Base.Messages (internalError)
> import Base.Types as BT
> import Base.Typing
> import Base.Utils (mapAccumM, concatMapM)

> import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
> import Env.Value (ValueEnv, ValueInfo (..), bindFun, bindGlobalInfo
>   , lookupValue, qualLookupValue)

\end{verbatim}
New identifiers may be introduced while desugaring pattern
declarations, case and $\lambda$-expressions, and list comprehensions.
As usual, we use a state monad transformer for generating unique
names. In addition, the state is also used for passing through the
type environment, which must be augmented with the types of these new
variables.
\begin{verbatim}

> data DesugarState = DesugarState
>   { moduleIdent :: ModuleIdent -- read-only
>   , tyConsEnv   :: TCEnv       -- read-only
>   , valueEnv    :: ValueEnv
>   , nextId      :: Integer     -- counter
>   }

> type DsM a = S.State DesugarState a

> getModuleIdent :: DsM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> getTyConsEnv :: DsM TCEnv
> getTyConsEnv = S.gets tyConsEnv

> getValueEnv :: DsM ValueEnv
> getValueEnv = S.gets valueEnv

> modifyValueEnv :: (ValueEnv -> ValueEnv) -> DsM ()
> modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

> getNextId :: DsM Integer
> getNextId = do
>   nid <- S.gets nextId
>   S.modify $ \ s -> s { nextId = succ nid }
>   return nid

\end{verbatim}
Generation of fresh names
\begin{verbatim}

> getTypeOf :: Typeable t => t -> DsM Type
> getTypeOf t = getValueEnv >>= \ tyEnv -> return (typeOf tyEnv t)

> freshIdent :: String -> Int -> TypeScheme -> DsM Ident
> freshIdent prefix arity ty = do
>   m <- getModuleIdent
>   x <- mkName prefix `liftM` getNextId
>   modifyValueEnv $ bindFun m x arity ty
>   return x
>   where mkName pre n = mkIdent $ pre ++ show n

> freshMonoTypeVar :: Typeable t => String -> t -> DsM Ident
> freshMonoTypeVar prefix t = getTypeOf t >>= \ ty ->
>   freshIdent prefix (arrowArity ty) (monoType ty)

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. In the current version, record declarations
are transformed into data types. The remaining type declarations are
not desugared and cannot occur in local declaration groups.
They are filtered out separately.

In order to use records within other modules, the export specification
of the module has to be extended with the selector and update functions of
all exported labels.

Actually, the transformation is slightly more general than necessary
as it allows value declarations at the top-level of a module.
\begin{verbatim}

> desugar :: ValueEnv -> TCEnv -> Module -> (Module, ValueEnv)
> desugar tyEnv tcEnv (Module m es is ds) = (Module m es is ds', valueEnv s')
>   where (ds', s') = S.runState (desugarModuleDecls ds)
>                                (DesugarState m tcEnv tyEnv 1)

> desugarModuleDecls :: [Decl] -> DsM [Decl]
> desugarModuleDecls ds = do
>   ds'  <- concatMapM dsRecordDecl ds -- convert record decls to data decls
>   ds'' <- dsDeclGroup ds'
>   return $ filter isTypeDecl ds' ++ ds''

\end{verbatim}
Within a declaration group, all type signatures and evaluation
annotations are discarded. First, the patterns occurring in the left
hand sides are desugared. Due to lazy patterns, this may add further
declarations to the group that must be desugared as well.
\begin{verbatim}

> dsDeclGroup :: [Decl] -> DsM [Decl]
> dsDeclGroup ds = concatMapM dsDeclLhs valDecls >>= mapM dsDeclRhs
>  where valDecls = filter isValueDecl ds

> dsDeclLhs :: Decl -> DsM [Decl]
> dsDeclLhs (PatternDecl p t rhs) = do
>   (ds', t') <- dsPattern p [] t
>   dss'      <- mapM dsDeclLhs ds'
>   return $ PatternDecl p t' rhs : concat dss'
> dsDeclLhs (ExternalDecl   p fs) = mapM (genForeignDecl p) fs
> dsDeclLhs d                     = return [d]

> genForeignDecl :: Position -> Ident -> DsM Decl
> genForeignDecl p f = do
>   m     <- getModuleIdent
>   ty    <- fromType `liftM` (getTypeOf $ Variable $ qual m f)
>   return $ ForeignDecl p CallConvPrimitive (Just $ idName f) f ty
>   where qual m f'
>          | hasGlobalScope f' = qualifyWith m f'
>          | otherwise         = qualify f'

\end{verbatim}
After desugaring its right hand side, each equation is $\eta$-expanded
by adding as many variables as necessary to the argument list and
applying the right hand side to those variables ({\em Note:} $\eta$-expansion
is disabled in the version for PAKCS).
Furthermore every occurrence of a record type within the type of a function
is simplified to the corresponding type constructor from the record
declaration. This is possible because currently records must not be empty
and a record label belongs to only one record declaration.
\begin{verbatim}

> dsDeclRhs :: Decl -> DsM Decl
> dsDeclRhs (FunctionDecl     p f eqs) =
>   FunctionDecl p f `liftM` mapM dsEquation eqs
> dsDeclRhs (PatternDecl      p t rhs) =
>   PatternDecl p t `liftM` dsRhs p id rhs
> dsDeclRhs (ForeignDecl p cc ie f ty) =
>   return $ ForeignDecl p cc (ie `mplus` Just (idName f)) f ty
> dsDeclRhs vars@(FreeDecl        _ _) = return vars
> dsDeclRhs _ = error "Desugar.dsDeclRhs: no pattern match"

> dsEquation :: Equation -> DsM Equation
> dsEquation (Equation p lhs rhs) = do
>   (ds1, cs1, ts1) <- dsFunctionalPatterns p     ts
>   (cs2     , ts2) <- dsNonLinearity             ts1
>   (ds2     , ts3) <- mapAccumM (dsPattern p) [] ts2
>   rhs1            <- dsRhs p (addConstraints (cs1 ++ cs2))
>                    $ addDecls (ds1 ++ ds2) $ rhs
>   return $ Equation p (FunLhs f ts3) rhs1
>   where (f, ts) = flatLhs lhs

> -- Desugaring of non-linear pattern
> -- The desugaring traverses a pattern in depth-first order and collects
> -- all variables. If it encounters a variable which has been previously
> -- introduced, the second occurrence is changed to a fresh variable
> -- and a new pair (newvar, oldvar) is saved to generate constraints later.
> -- /Note:/ Non-linear patterns in functional patterns are not desugared,
> -- as this special case is handled later.
> dsNonLinearity :: [Pattern] -> DsM ([Expression], [Pattern])
> dsNonLinearity ts = do
>   ((_, cs), ts') <- mapAccumM dsNonLinear (Set.empty, []) ts
>   return (reverse cs, ts')

> type NonLinearEnv = (Set.Set Ident, [Expression])

> dsNonLinear :: NonLinearEnv -> Pattern -> DsM (NonLinearEnv, Pattern)
> dsNonLinear env l@(LiteralPattern        _) = return (env, l)
> dsNonLinear env n@(NegativePattern     _ _) = return (env, n)
> dsNonLinear env t@(VariablePattern       v)
>   | v `Set.member` vis = do
>     v' <- freshMonoTypeVar "_#nonlinear" t
>     return ((vis, (mkVar v =:= mkVar v') : ren), VariablePattern v')
>   | otherwise        = return ((Set.insert v vis, ren), t)
>   where (vis, ren) = env
> dsNonLinear env (ConstructorPattern   c ts) = do
>   (env', ts') <- mapAccumM dsNonLinear env ts
>   return (env', ConstructorPattern c ts')
> dsNonLinear env (InfixPattern     t1 op t2) = do
>   (env1, t1') <- dsNonLinear env  t1
>   (env2, t2') <- dsNonLinear env1 t2
>   return (env2, InfixPattern t1' op t2')
> dsNonLinear env (ParenPattern            t) = do
>   (env', t') <- dsNonLinear env t
>   return (env', ParenPattern t')
> dsNonLinear env (TuplePattern       pos ts) = do
>   (env', ts') <- mapAccumM dsNonLinear env ts
>   return (env', TuplePattern pos ts')
> dsNonLinear env (ListPattern        pos ts) = do
>   (env', ts') <- mapAccumM dsNonLinear env ts
>   return (env', ListPattern pos ts')
> dsNonLinear env (AsPattern             v t) = do
>   (env1, VariablePattern v') <- dsNonLinear env (VariablePattern v)
>   (env2, t') <- dsNonLinear env1 t
>   return (env2, AsPattern v' t')
> dsNonLinear env (LazyPattern           r t) = do
>   (env', t') <- dsNonLinear env t
>   return (env', LazyPattern r t')
> dsNonLinear env (FunctionPattern      f ts) = do
>   (env', ts') <- mapAccumM dsNonLinear env ts
>   return (env', FunctionPattern f ts')
> dsNonLinear env (InfixFuncPattern t1 op t2) = do
>   (env1, t1') <- dsNonLinear env  t1
>   (env2, t2') <- dsNonLinear env1 t2
>   return (env2, InfixFuncPattern t1' op t2')
> dsNonLinear env (RecordPattern        fs r) = do
>   (env1, fs') <- mapAccumM dsField env fs
>   return (env1, RecordPattern fs' r)
>   where dsField e (Field p i t) = do
>           (e', t') <- dsNonLinear e t
>           return (e', Field p i t')

\end{verbatim}
The transformation of patterns is straight forward except for lazy
patterns. A lazy pattern \texttt{\~}$t$ is replaced by a fresh
variable $v$ and a new local declaration $t$~\texttt{=}~$v$ in the
scope of the pattern. In addition, as-patterns $v$\texttt{@}$t$ where
$t$ is a variable or an as-pattern are replaced by $t$ in combination
with a local declaration for $v$.
\begin{verbatim}

> dsPattern :: Position -> [Decl] -> Pattern -> DsM ([Decl], Pattern)
> dsPattern p ds (LiteralPattern         l) = do
>   dl <- dsLiteral l
>   case dl of
>     Left  l'     -> return (ds, LiteralPattern l')
>     Right (rs,ls) -> dsPattern p ds $ ListPattern rs $ map LiteralPattern ls
> dsPattern p ds (NegativePattern      _ l) =
>   dsPattern p ds (LiteralPattern (negateLiteral l))
> dsPattern _ ds v@(VariablePattern      _) = return (ds, v)
> dsPattern p ds (ConstructorPattern c [t]) = do
>     tyEnv <- getValueEnv
>     liftM (if isNewtypeConstr tyEnv c then id else second (constrPat c))
>           (dsPattern p ds t)
>   where constrPat c' t' = ConstructorPattern c' [t']
> dsPattern p ds (ConstructorPattern c ts) =
>   liftM (second (ConstructorPattern c)) (mapAccumM (dsPattern p) ds ts)
> dsPattern p ds (InfixPattern t1 op t2) =
>   dsPattern p ds (ConstructorPattern op [t1,t2])
> dsPattern p ds (ParenPattern      t) = dsPattern p ds t
> dsPattern p ds (TuplePattern pos ts) =
>   dsPattern p ds (ConstructorPattern (tupleConstr ts) ts)
>   where tupleConstr ts' = addRef pos $
>                          if null ts' then qUnitId else qTupleId (length ts')
> dsPattern p ds (ListPattern pos ts) =
>   liftM (second (dsList pos cons nil)) (mapAccumM (dsPattern p) ds ts)
>   where nil  p' = ConstructorPattern (addRef p' qNilId) []
>         cons p' t ts' = ConstructorPattern (addRef p' qConsId) [t,ts']
> dsPattern p ds (AsPattern   v t) = liftM (dsAs p v) (dsPattern p ds t)
> dsPattern p ds (LazyPattern r t) = dsLazy r p ds t
> dsPattern p ds (FunctionPattern f ts) =
>   liftM (second (FunctionPattern f)) (mapAccumM (dsPattern p) ds ts)
> dsPattern p ds (InfixFuncPattern t1 f t2) =
>   dsPattern p ds (FunctionPattern f [t1,t2])
> dsPattern p ds (RecordPattern fs _)
>   | null fs   = internalError "Desugar.dsPattern: empty record"
>   | otherwise = do
>     r   <- recordFromField (fieldLabel (head fs))
>     fs' <- (map fst . snd) `liftM` lookupRecord r
>     let ts = map (dsLabel (map field2Tuple fs)) fs'
>     dsPattern p ds (ConstructorPattern r ts)
>   where dsLabel fs' l = fromMaybe (VariablePattern anonId) (lookup l fs')

> dsLiteral :: Literal -> DsM (Either Literal ([SrcRef], [Literal]))
> dsLiteral c@(Char             _ _) = return $ Left c
> dsLiteral (Int                v i) = (Left . fixType) `liftM` getValueEnv
>   where fixType tyEnv
>           | typeOf tyEnv v == floatType
>           = Float (srcRefOf $ idPosition v) (fromIntegral i)
>           | otherwise = Int v i
> dsLiteral f@(Float            _ _) = return $ Left f
> dsLiteral (String (SrcRef [i]) cs) = return $ Right
>   (consRefs i cs, zipWith (Char . SrcRef . (:[])) [i, i + 2 ..] cs)
>   where consRefs r []     = [SrcRef [r]]
>         consRefs r (_:xs) = let r' = r + 2
>                             in  r' `seq` (SrcRef [r'] : consRefs r' xs)
> dsLiteral (String is _) = internalError $
>   "Desugar.dsLiteral: " ++ "wrong source ref for string "  ++ show is

> dsList :: [SrcRef] -> (SrcRef -> b -> b -> b) -> (SrcRef -> b) -> [b] -> b
> dsList pos cons nil xs = snd (foldr cons' nil' xs)
>   where rNil : rCs = reverse pos
>         nil'                 = (rCs , nil rNil)
>         cons' t (rC:rCs',ts) = (rCs', cons rC t ts)
>         cons' _ ([],_) = error "Desugar.dsList.cons': empty list"

> dsAs :: Position -> Ident -> ([Decl], Pattern) -> ([Decl], Pattern)
> dsAs p v (ds, t) = case t of
>   VariablePattern v' -> (varDecl p v (mkVar v') : ds, t)
>   AsPattern     v' _ -> (varDecl p v (mkVar v') : ds, t)
>   _                  -> (ds, AsPattern v t)

> dsLazy :: SrcRef -> Position -> [Decl] -> Pattern -> DsM ([Decl], Pattern)
> dsLazy pos p ds t = case t of
>   VariablePattern   _ -> return (ds, t)
>   ParenPattern     t' -> dsLazy pos p ds t'
>   AsPattern      v t' -> dsAs p v `liftM` dsLazy pos p ds t'
>   LazyPattern pos' t' -> dsLazy pos' p ds t'
>   _                   -> do
>    v' <- addPositionIdent (AST pos) `liftM` freshMonoTypeVar "_#lazy" t
>    return (patDecl p { astRef = pos } t (mkVar v') : ds, VariablePattern v')

> negateLiteral :: Literal -> Literal
> negateLiteral (Int    v i) = Int   v  (-i)
> negateLiteral (Float p' f) = Float p' (-f)
> negateLiteral _            = internalError "Desugar.negateLiteral"

\end{verbatim}
A list of boolean guards is expanded into a nested if-then-else
expression, whereas a constraint guard is replaced by a case
expression. Note that if the guard type is \texttt{Success} only a
single guard is allowed for each equation.\footnote{This change was
introduced in version 0.8 of the Curry report.} We check for the
type \texttt{Bool} of the guard because the guard's type defaults to
\texttt{Success} if it is not restricted by the guard expression.
\begin{verbatim}

> dsRhs :: Position -> (Expression -> Expression) -> Rhs -> DsM Rhs
> dsRhs p f rhs = do
>   e' <- expandRhs prelFailed f rhs >>= dsExpr p
>   return (SimpleRhs p e' [])

> expandRhs :: Expression -> (Expression -> Expression) -> Rhs -> DsM Expression
> expandRhs _  f (SimpleRhs _ e ds) = return $ Let ds (f e)
> expandRhs e0 f (GuardedRhs es ds) = (Let ds . f) `liftM` expandGuards e0 es

> expandGuards :: Expression -> [CondExpr] -> DsM Expression
> expandGuards e0 es = do
>   tyEnv <- getValueEnv
>   return $ if booleanGuards tyEnv es
>               then foldr mkIfThenElse e0 es
>               else mkCond es
>   where mkIfThenElse (CondExpr p g e) = IfThenElse (srcRefOf p) g e
>         mkCond       [CondExpr _ g e] = apply prelCond [g, e]
>         mkCond _ = error "Desugar.expandGuards.mkCond: non-unary list"

> addConstraints :: [Expression] -> Expression -> Expression
> addConstraints cs e
>   | null cs   = e
>   | otherwise = apply prelCond [foldr1 (&) cs, e]

> booleanGuards :: ValueEnv -> [CondExpr] -> Bool
> booleanGuards _     []                    = False
> booleanGuards tyEnv (CondExpr _ g _ : es) =
>   not (null es) || typeOf tyEnv g == boolType

> dsExpr :: Position -> Expression -> DsM Expression
> dsExpr p (Literal l) =
>   dsLiteral l >>=
>   either (return . Literal) (\ (pos, ls) -> dsExpr p $ List pos $ map Literal ls)
> dsExpr _ var@(Variable v)
>   | isAnonId (unqualify v) = return prelUnknown
>       -- v' <- getValueEnv >>= freshIdent "_#anonfree" . polyType . flip typeOf var
>       -- dsExpr p $ Let [ExtraVariables p [v']] $ mkVar v'
>   | otherwise              = return var
> dsExpr _ c@(Constructor _) = return c
> dsExpr p (Paren         e) = dsExpr p e
> dsExpr p (Typed   e cx ty) = liftM3 Typed (dsExpr p e) (return cx) (return ty)
> dsExpr p (Tuple    pos es) =
>   apply (Constructor $ tupleConstr es) `liftM` mapM (dsExpr p) es
>   where tupleConstr es1 = addRef pos $ if null es1 then qUnitId else qTupleId (length es1)
> dsExpr p (List pos es) =
>   dsList pos cons nil `liftM` mapM (dsExpr p) es
>   where nil p'  = Constructor (addRef p' qNilId)
>         cons p' = Apply . Apply (Constructor $ addRef p' qConsId)
> dsExpr p (ListCompr r e []    ) = dsExpr p (List [r,r] [e])
> dsExpr p (ListCompr r e (q:qs)) = dsQual p q (ListCompr r e qs)
> dsExpr p (EnumFrom e) =
>   Apply prelEnumFrom `liftM` dsExpr p e
> dsExpr p (EnumFromThen e1 e2) =
>   apply prelEnumFromThen `liftM` mapM (dsExpr p) [e1, e2]
> dsExpr p (EnumFromTo e1 e2) =
>   apply prelEnumFromTo `liftM` mapM (dsExpr p) [e1, e2]
> dsExpr p (EnumFromThenTo e1 e2 e3) =
>   apply prelEnumFromThenTo `liftM` mapM (dsExpr p) [e1, e2, e3]
> dsExpr p (UnaryMinus op e) = do
>   ty <- getTypeOf e
>   Apply (unaryMinus op ty) `liftM` dsExpr p e
>   where
>   unaryMinus op1 ty'
>     | op1 ==  minusId = if ty' == floatType then prelNegateFloat else prelNegate
>     | op1 == fminusId = prelNegateFloat
>     | otherwise       = internalError "Desugar.unaryMinus"
> dsExpr p (Apply (Constructor c) e) = do
>   tyEnv <- getValueEnv
>   liftM (if isNewtypeConstr tyEnv c then id else (Apply (Constructor c)))
>         (dsExpr p e)
> dsExpr p (Apply e1 e2) = do
>   liftM2 Apply (dsExpr p e1) (dsExpr p e2)
> dsExpr p (InfixApply e1 op e2) = do
>   op' <- dsExpr p (infixOp op)
>   e1' <- dsExpr p e1
>   e2' <- dsExpr p e2
>   return $ apply op' [e1', e2']
> dsExpr p (LeftSection e op) = do
>   liftM2 Apply (dsExpr p (infixOp op)) (dsExpr p e)
> dsExpr p (RightSection op e) = do
>   op' <- dsExpr p (infixOp op)
>   e' <- dsExpr p e
>   return $ apply prelFlip [op', e']
> dsExpr p expr@(Lambda r ts e) = do
>   ty <- getTypeOf expr
>   f  <- freshIdent "_#lambda" (length ts) (polyType ty)
>   dsExpr p $ Let [funDecl (AST r) f ts e] $ mkVar f
> dsExpr p (Let ds e) = do
>   ds' <- dsDeclGroup ds
>   e' <- dsExpr p e
>   return (if null ds' then e' else Let ds' e')
> dsExpr p (Do sts e) =
>   dsExpr p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr r e1) e' = apply (prelBind_ r) [e1,e']
>         desugarStmt (StmtBind r t e1) e' = apply (prelBind r) [e1,Lambda r [t] e']
>         desugarStmt (StmtDecl ds) e' = Let ds e'
> dsExpr p (IfThenElse r e1 e2 e3) = do
>   e1' <- dsExpr p e1
>   e2' <- dsExpr p e2
>   e3' <- dsExpr p e3
>   return (Case r Rigid e1'
>           [caseAlt p truePattern e2', caseAlt p falsePattern e3'])
> dsExpr p (Case r ct e alts)
>   | null alts = return prelFailed
>   | otherwise = do
>     m  <- getModuleIdent
>     e' <- dsExpr p e
>     v  <- freshMonoTypeVar "_#case" e
>     alts'  <- mapM dsAltLhs alts
>     alts'' <- mapM (expandAlt v ct) (init (tails alts')) >>= mapM dsAltRhs
>     return (mkCase m v e' alts'')
>   where
>   mkCase m1 v e1 alts1
>     | v `elem` qfv m1 alts1 = Let [varDecl p v e1] (Case r ct (mkVar v) alts1)
>     | otherwise             = Case r ct e1 alts1
> dsExpr p (RecordConstr fs)
>   | null fs   = internalError "Desugar.dsExpr: empty record construction"
>   | otherwise = do
>     r <- recordFromField (fieldLabel (head fs))
>     dsRecordConstr p r (map field2Tuple fs)
> dsExpr p (RecordSelection e l) = do
>   m <- getModuleIdent
>   r <- recordFromField l
>   dsExpr p (Apply (Variable (qualRecSelectorId m r l)) e)
> dsExpr p (RecordUpdate fs rexpr)
>   | null fs   = internalError "Desugar.dsExpr: empty record update"
>   | otherwise = do
>     r <- recordFromField (fieldLabel (head fs))
>     dsRecordUpdate p r rexpr (map field2Tuple fs)

\end{verbatim}
If an alternative in a case expression has boolean guards and all of
these guards return \texttt{False}, the enclosing case expression does
not fail but continues to match the remaining alternatives against the
selector expression. In order to implement this semantics, which is
compatible with Haskell, we expand an alternative with boolean guards
such that it evaluates a case expression with the remaining cases that
are compatible with the matched pattern when the guards fail.
\begin{verbatim}

> dsAltLhs :: Alt -> DsM Alt
> dsAltLhs (Alt p t rhs) = do
>   (ds', t') <- dsPattern p [] t
>   return $ Alt p t' (addDecls ds' rhs)

> dsAltRhs :: Alt -> DsM Alt
> dsAltRhs (Alt p t rhs) = Alt p t `liftM` dsRhs p id rhs

> expandAlt :: Ident -> CaseType -> [Alt] -> DsM Alt
> expandAlt _ _  []                   = error "Desugar.expandAlt: empty list"
> expandAlt v ct (Alt p t rhs : alts) = caseAlt p t `liftM` expandRhs e0 id rhs
>   where
>   e0 | ct == Flex = prelFailed
>      | otherwise  = Case (srcRefOf p) ct (mkVar v)
>                          (filter (isCompatible t . altPattern) alts)
>   altPattern (Alt _ t1 _) = t1

> isCompatible :: Pattern -> Pattern -> Bool
> isCompatible (VariablePattern _) _                   = True
> isCompatible _                   (VariablePattern _) = True
> isCompatible (AsPattern    _ t1) t2                  = isCompatible t1 t2
> isCompatible t1                  (AsPattern    _ t2) = isCompatible t1 t2
> isCompatible (ConstructorPattern c1 ts1) (ConstructorPattern c2 ts2)
>   = and ((c1 == c2) : zipWith isCompatible ts1 ts2)
> isCompatible (LiteralPattern         l1) (LiteralPattern         l2)
>   = canon l1 == canon l2
>   where canon (Int _ i) = Int anonId i
>         canon l         = l
> isCompatible _                    _                  = False

\end{verbatim}
The frontend provides several extensions of the Curry functionality, which
have to be desugared as well. This part transforms the following extensions:
\begin{itemize}
\item runction patterns
\item records
\end{itemize}
\begin{verbatim}

Function Patterns
=================

> dsFunctionalPatterns :: Position -> [Pattern] -> DsM ([Decl], [Expression], [Pattern])
> dsFunctionalPatterns p ts = do
>   (bs, ts') <- mapAccumM elimFP [] ts
>   let (ds, cs) = genFPExpr p (bv ts') (reverse bs)
>   return (ds, cs, ts')

> type LazyBinding = (Pattern, Ident)

> elimFP :: [LazyBinding] -> Pattern -> DsM ([LazyBinding], Pattern)
> elimFP bs p@(LiteralPattern        _) = return (bs, p)
> elimFP bs p@(NegativePattern     _ _) = return (bs, p)
> elimFP bs p@(VariablePattern       _) = return (bs, p)
> elimFP bs (ConstructorPattern   c ts)
>   = second (ConstructorPattern c) `liftM` mapAccumM elimFP bs ts
> elimFP bs (InfixPattern     t1 op t2) = do
>   (bs', [t1',t2']) <- mapAccumM elimFP bs [t1,t2]
>   return (bs', InfixPattern t1' op t2')
> elimFP bs (ParenPattern            t)
>  = second ParenPattern `liftM` elimFP bs t
> elimFP bs (TuplePattern       pos ts)
>   = second (TuplePattern pos) `liftM` mapAccumM elimFP bs ts
> elimFP bs (ListPattern        pos ts)
>   = second (ListPattern pos) `liftM` mapAccumM elimFP bs ts
> elimFP bs (AsPattern             v t)
>  = second (AsPattern v) `liftM` elimFP bs t
> elimFP bs (LazyPattern           r t)
>  = second (LazyPattern r) `liftM` elimFP bs t
> elimFP bs p@(FunctionPattern     _ _) = do
>  v <- freshMonoTypeVar "_#funpatt" p
>  return ((p, v) : bs, VariablePattern v)
> elimFP bs p@(InfixFuncPattern  _ _ _) = do
>  v <- freshMonoTypeVar "_#funpatt" p
>  return ((p, v) : bs, VariablePattern v)
> elimFP bs (RecordPattern        fs r) = do
>   second (flip RecordPattern r) `liftM` mapAccumM elimField bs fs
>   where elimField b (Field p i t) = second (Field p i) `liftM` elimFP b t

> genFPExpr :: Position -> [Ident] -> [LazyBinding] -> ([Decl], [Expression])
> genFPExpr p vs bs
>   | null bs   = ([]               , [])
>   | null free = ([]               , cs)
>   | otherwise = ([FreeDecl p free], cs)
>   where
>   mkLB (t, v) = let (t', es) = fp2Expr t
>                 in  (t' =:<= mkVar v) : es
>   cs       = concatMap mkLB bs
>   free     = nub $ filter (not . isAnonId) $ bv (map fst bs) \\ vs

> fp2Expr :: Pattern -> (Expression, [Expression])
> fp2Expr (LiteralPattern          l) = (Literal l, [])
> fp2Expr (NegativePattern       _ l) = (Literal (negateLiteral l), [])
> fp2Expr (VariablePattern         v) = (mkVar v, [])
> fp2Expr (ConstructorPattern   c ts) =
>   let (ts', ess) = unzip $ map fp2Expr ts
>   in  (apply (Constructor c) ts', concat ess)
> fp2Expr (InfixPattern     t1 op t2) =
>   let (t1', es1) = fp2Expr t1
>       (t2', es2) = fp2Expr t2
>   in  (InfixApply t1' (InfixConstr op) t2', es1 ++ es2)
> fp2Expr (ParenPattern            t) = first Paren (fp2Expr t)
> fp2Expr (TuplePattern         r ts) =
>   let (ts', ess) = unzip $ map fp2Expr ts
>   in  (Tuple r ts', concat ess)
> fp2Expr (ListPattern         rs ts) =
>   let (ts', ess) = unzip $ map fp2Expr ts
>   in  (List rs ts', concat ess)
> fp2Expr (FunctionPattern      f ts) =
>   let (ts', ess) = unzip $ map fp2Expr ts
>   in  (apply (Variable f) ts', concat ess)
> fp2Expr (InfixFuncPattern t1 op t2) =
>   let (t1', es1) = fp2Expr t1
>       (t2', es2) = fp2Expr t2
>   in  (InfixApply t1' (InfixOp op) t2', es1 ++ es2)
> fp2Expr (AsPattern             v t) =
>   let (t', es) = fp2Expr t
>   in  (mkVar v, (t' =:<= mkVar v):es)
> fp2Expr t                           = internalError $
>   "Desugar.fp2Expr: Unexpected constructor term: " ++ show t

Desugaring of Records
=====================

> recordFromField :: Ident -> DsM QualIdent
> recordFromField lbl = do
>   tyEnv <- getValueEnv
>   case lookupValue lbl tyEnv of
>     [Label _ r _] -> return r
>     _             -> internalError $
>       "Desugar.recordFromField: unknown label: " ++ show lbl

> lookupRecord :: QualIdent -> DsM (Int, [(Ident, Type)])
> lookupRecord r = do
>   tcEnv <- getTyConsEnv
>   case qualLookupTC r tcEnv of
>     [AliasType _ n (TypeRecord fs _)] -> return (n, fs)
>     _                                 ->
>       internalError $ "Desugar.lookupRecord: no record: " ++ show r

> dsRecordDecl :: Decl -> DsM [Decl]
> dsRecordDecl (TypeDecl p r vs (RecordType fss _)) = do
>   m     <- getModuleIdent
>   let qr = qualifyWith m r
>   (n, fs') <- lookupRecord qr
>   let tys   = concatMap (\ (ls, ty) -> replicate (length ls) ty) fss
>       --tys' = map (elimRecordTypes tyEnv) tys
>       rdecl = DataDecl p r vs [ConstrDecl p [] r tys]
>       rty'  = TypeConstructor qr (map TypeVariable [0 .. n - 1])
>       rcts' = ForAllExist BT.emptyContext 0 n (foldr TypeArrow rty' (map snd fs'))
>   rfuncs <- mapM (genRecordFuncs p qr rty' (map fst fs')) fs'
>   modifyValueEnv
>       (bindGlobalInfo (flip DataConstructor (length tys)) m r rcts')
>   return $ rdecl : concat rfuncs
> dsRecordDecl d = return [d]

> genRecordFuncs :: Position -> QualIdent -> Type -> [Ident] -> (Ident, Type)
>                -> DsM [Decl]
> genRecordFuncs p r rty ls (l, ty) = do
>   m <- getModuleIdent
>   let (selId, selFunc) = genSelectFunc p r ls l
>       (updId, updFunc) = genUpdateFunc p r ls l
>       selType = polyType (TypeArrow rty ty)
>       updType = polyType (TypeArrow rty $ TypeArrow ty rty)
>   modifyValueEnv (bindFun m selId 1 selType . bindFun m updId 2 updType)
>   return [selFunc, updFunc]

> genSelectFunc :: Position -> QualIdent -> [Ident] -> Ident -> (Ident, Decl)
> genSelectFunc p r ls l = (selId, funDecl p selId [cpatt] (mkVar l))
>   where
>   selId  = recSelectorId r l
>   cpatt  = ConstructorPattern r (map VariablePattern ls)

> genUpdateFunc :: Position -> QualIdent -> [Ident] -> Ident -> (Ident, Decl)
> genUpdateFunc p r ls l = (updId, funDecl p updId [cpatt1, cpatt2] cexpr)
>   where
>   updId  = recUpdateId r l
>   vs     = [ VariablePattern (if v == l then anonId else v) | v <- ls]
>   cpatt1 = ConstructorPattern r vs
>   cpatt2 = VariablePattern l
>   cexpr  = apply (Constructor r) (map mkVar ls)

> dsRecordConstr :: Position -> QualIdent -> [(Ident, Expression)]
>                -> DsM Expression
> dsRecordConstr p r fs = do
>   fs' <- (map fst . snd) `liftM` lookupRecord r
>   let cts = map (\ l -> fromMaybe (internalError "Desugar.dsRecordConstr")
>                             (lookup l fs)) fs'
>   dsExpr p (apply (Constructor r) cts)

> dsRecordUpdate :: Position -> QualIdent -> Expression
>                -> [(Ident, Expression)] -> DsM Expression
> dsRecordUpdate p r rexpr fs = do
>   m <- getModuleIdent
>   dsExpr p (foldl (genRecordUpdate m r) rexpr fs)
>   where
>   genRecordUpdate m1 r1 rexpr1 (l,e) =
>    apply (Variable $ qualRecUpdateId m1 r1 l) [rexpr1, e]

\end{verbatim}
In general, a list comprehension of the form
\texttt{[}$e$~\texttt{|}~$t$~\texttt{<-}~$l$\texttt{,}~\emph{qs}\texttt{]}
is transformed into an expression \texttt{foldr}~$f$~\texttt{[]}~$l$ where $f$
is a new function defined as
\begin{quote}
  \begin{tabbing}
    $f$ $x$ \emph{xs} \texttt{=} \\
    \quad \= \texttt{case} $x$ \texttt{of} \\
          \> \quad \= $t$ \texttt{->} \texttt{[}$e$ \texttt{|} \emph{qs}\texttt{]} \texttt{++} \emph{xs} \\
          \>       \> \texttt{\_} \texttt{->} \emph{xs}
  \end{tabbing}
\end{quote}
Note that this translation evaluates the elements of $l$ rigidly,
whereas the translation given in the Curry report is flexible.
However, it does not seem very useful to have the comprehension
generate instances of $t$ which do not contribute to the list.

Actually, we generate slightly better code in a few special cases.
When $t$ is a plain variable, the \texttt{case} expression degenerates
into a let-binding and the auxiliary function thus becomes an alias
for \texttt{(++)}. Instead of \texttt{foldr~(++)} we use the
equivalent prelude function \texttt{concatMap}. In addition, if the
remaining list comprehension in the body of the auxiliary function has
no qualifiers -- i.e., if it is equivalent to \texttt{[$e$]} -- we
avoid the construction of the singleton list by calling \texttt{(:)}
instead of \texttt{(++)} and \texttt{map} in place of
\texttt{concatMap}, respectively. -}
\begin{verbatim}

> dsQual :: Position -> Statement -> Expression -> DsM Expression
> dsQual p (StmtExpr   r b) e = dsExpr p (IfThenElse r b e (List [r] []))
> dsQual p (StmtDecl    ds) e = dsExpr p (Let ds e)
> dsQual p (StmtBind r t l) e
>   | isVarPattern t = dsExpr p (qualExpr t e l)
>   | otherwise      = do
>     v   <- addRefId r `liftM` freshMonoTypeVar "_#var" t
>     l'  <- addRefId r `liftM` freshMonoTypeVar "_#var" e
>     dsExpr p (apply (prelFoldr r) [foldFunct v l' e, List [r] [], l])
>   where
>   qualExpr v (ListCompr _ e1 []) l1
>     = apply (prelMap r) [Lambda r [v] e1,l1]
>   qualExpr v e1                  l1
>     = apply (prelConcatMap r) [Lambda r [v] e1,l1]
>   foldFunct v l1 e1
>     = Lambda r (map VariablePattern [v,l1])
>        (Case r Rigid (mkVar v)
>           [ caseAlt p t (append e1 (mkVar l1))
>           , caseAlt p (VariablePattern v) (mkVar l1)])
>
>   append (ListCompr _ e1 []) l1 = apply (Constructor $ addRef r $ qConsId)
>                                         [e1,l1]
>   append e1                  l1 = apply (prelAppend r) [e1,l1]

\end{verbatim}
Prelude entities
\begin{verbatim}

> prelBind :: SrcRef -> Expression
> prelBind = prel ">>="

> prelBind_ :: SrcRef -> Expression
> prelBind_ = prel ">>"

> prelFlip :: Expression
> prelFlip = Variable $ preludeIdent "flip"

> prelEnumFrom :: Expression
> prelEnumFrom = Variable $ preludeIdent "enumFrom"

> prelEnumFromTo :: Expression
> prelEnumFromTo = Variable $ preludeIdent "enumFromTo"

> prelEnumFromThen :: Expression
> prelEnumFromThen = Variable $ preludeIdent "enumFromThen"

> prelEnumFromThenTo :: Expression
> prelEnumFromThenTo = Variable $ preludeIdent "enumFromThenTo"

> prelFailed :: Expression
> prelFailed = Variable $ preludeIdent "failed"

> prelUnknown :: Expression
> prelUnknown = Variable $ preludeIdent "unknown"

> prelMap :: SrcRef -> Expression
> prelMap r = Variable $ addRef r $ preludeIdent "map"

> prelFoldr :: SrcRef -> Expression
> prelFoldr = prel "foldr"

> prelAppend :: SrcRef -> Expression
> prelAppend = prel "++"

> prelConcatMap :: SrcRef -> Expression
> prelConcatMap = prel "concatMap"

> prelNegate :: Expression
> prelNegate = Variable $ preludeIdent "negate"

> prelNegateFloat :: Expression
> prelNegateFloat = Variable $ preludeIdent "negateFloat"

> prelCond :: Expression
> prelCond = Variable $ preludeIdent "cond"

> (=:<=) :: Expression -> Expression -> Expression
> e1 =:<= e2 = apply prelFPEq [e1, e2]

> prelFPEq :: Expression
> prelFPEq = Variable $ preludeIdent "=:<="

> prelConj :: Expression
> prelConj = Variable $ preludeIdent "&"

> (=:=) :: Expression -> Expression -> Expression
> e1 =:= e2 = apply prelSEq [e1, e2]

> prelSEq :: Expression
> prelSEq = Variable $ preludeIdent "=:="

> (&) :: Expression -> Expression -> Expression
> e1 & e2 = apply prelConj [e1, e2]

> prel :: String -> SrcRef -> Expression
> prel s r = Variable $ addRef r $ preludeIdent s

> truePattern :: Pattern
> truePattern = ConstructorPattern qTrueId []

> falsePattern :: Pattern
> falsePattern = ConstructorPattern qFalseId []

> preludeIdent :: String -> QualIdent
> preludeIdent = qualifyWith preludeMIdent . mkIdent

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
> isNewtypeConstr tyEnv c = case qualLookupValue c tyEnv of
>   [NewtypeConstructor _ _] -> True
>   [DataConstructor  _ _ _] -> False
>   x -> internalError $ "Transformations.Desugar.isNewtypeConstr: "
>                         ++ show c ++ " is " ++ show x

> isVarPattern :: Pattern -> Bool
> isVarPattern (VariablePattern _) = True
> isVarPattern (ParenPattern    t) = isVarPattern t
> isVarPattern (AsPattern     _ t) = isVarPattern t
> isVarPattern (LazyPattern   _ _) = True
> isVarPattern _                   = False

> funDecl :: Position -> Ident -> [Pattern] -> Expression -> Decl
> funDecl p f ts e = FunctionDecl p f
>   [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> patDecl :: Position -> Pattern -> Expression -> Decl
> patDecl p t e = PatternDecl p t (SimpleRhs p e [])

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p = patDecl p . VariablePattern

> addDecls :: [Decl] -> Rhs -> Rhs
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

> caseAlt :: Position -> Pattern -> Expression -> Alt
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> apply :: Expression -> [Expression] -> Expression
> apply = foldl Apply

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

\end{verbatim}
