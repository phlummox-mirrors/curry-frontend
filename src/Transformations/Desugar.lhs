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

> import Control.Arrow (second)
> import Control.Monad (liftM, liftM2, mplus)
> import qualified Control.Monad.State as S (State, evalState, gets, modify)
> import Data.List (tails)
> import Data.Maybe (fromMaybe)

> import Curry.Base.Ident
> import Curry.Base.Position
> import Curry.Syntax

> import Base.Expr
> import Base.CurryTypes (fromType)
> import Base.Messages (internalError)
> import Base.Types
> import Base.Typing
> import Base.Utils (mapAccumM)

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
>   { moduleIdent :: ModuleIdent
>   , tyConsEnv   :: TCEnv
>   , valueEnv    :: ValueEnv
>   , nextId      :: Integer
>   }

> type DsM a = S.State DesugarState a

> run :: DsM a -> DesugarState -> a
> run = S.evalState

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
The desugaring phase keeps only the type, function, and value
declarations of the module. In the current version record declarations
are transformed into data types. The remaining type declarations are
not desugared and cannot occur in local declaration groups.
They are filtered out separately.

In order to use records within other modules, the export specification
of the module has to be extended with the selector and update functions of
all exported labels.

Actually, the transformation is slightly more general than necessary
as it allows value declarations at the top-level of a module.
\begin{verbatim}

> desugar :: ValueEnv -> TCEnv -> Module -> (Module,ValueEnv)
> desugar tyEnv tcEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds', tyEnv') = run (desugarModuleDecls ds)
>                             (DesugarState m tcEnv tyEnv 1)

> desugarModuleDecls :: [Decl] -> DsM ([Decl], ValueEnv)
> desugarModuleDecls ds = do
>   ds'    <- concat `liftM` mapM desugarRecordDecl ds
>   ds''   <- desugarDeclGroup ds'
>   tyEnv' <- getValueEnv
>   return (filter isTypeDecl ds' ++ ds'', tyEnv')

\end{verbatim}
Within a declaration group, all type signatures and evaluation
annotations are discarded. First, the patterns occurring in the left
hand sides are desugared. Due to lazy patterns this may add further
declarations to the group that must be desugared as well.
\begin{verbatim}

> desugarDeclGroup :: [Decl] -> DsM [Decl]
> desugarDeclGroup ds = do
>   ds' <- concat `liftM` mapM desugarDeclLhs (filter isValueDecl ds)
>   mapM desugarDeclRhs ds'

> desugarDeclLhs :: Decl -> DsM [Decl]
> desugarDeclLhs (PatternDecl   p t rhs) = do
>   (ds',t') <- desugarTerm p [] t
>   dss'     <- mapM desugarDeclLhs ds'
>   return $ PatternDecl p t' rhs : concat dss'
> desugarDeclLhs (FlatExternalDecl p fs) = do
>   m <- getModuleIdent
>   tyEnv <- getValueEnv
>   return $ map (externalDecl tyEnv p m) fs
>   where
>   externalDecl tyEnv p' m f =
>    ExternalDecl p' CallConvPrimitive (Just (name f)) f
>      (fromType (typeOf tyEnv (Variable (qual m f))))
>   qual m f
>     | unRenameIdent f == f = qualifyWith m f
>     | otherwise            = qualify f
> desugarDeclLhs d = return [d]

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

> desugarDeclRhs :: Decl -> DsM Decl
> desugarDeclRhs (FunctionDecl      p f eqs) =
>   FunctionDecl p f `liftM` mapM desugarEquation eqs
> desugarDeclRhs (PatternDecl       p t rhs) =
>   PatternDecl p t `liftM` desugarRhs p rhs
> desugarDeclRhs (ExternalDecl p cc ie f ty) =
>   return $ ExternalDecl p cc (ie `mplus` Just (name f)) f ty
> desugarDeclRhs vars@(ExtraVariables   _ _) = return vars
> desugarDeclRhs _ = error "Desugar.desugarDeclRhs: no pattern match"

> desugarEquation :: Equation -> DsM Equation
> desugarEquation (Equation p lhs rhs) = do
>   (ds', ts')    <- mapAccumM (desugarTerm p) [] ts
>   rhs'          <- desugarRhs p $ addDecls ds' rhs
>   (ts'', rhs'') <- desugarFunctionPatterns p ts' rhs'
>   return $ Equation p (FunLhs f ts'') rhs''
>   where (f, ts) = flatLhs lhs

\end{verbatim}
The transformation of patterns is straight forward except for lazy
patterns. A lazy pattern \texttt{\~}$t$ is replaced by a fresh
variable $v$ and a new local declaration $t$~\texttt{=}~$v$ in the
scope of the pattern. In addition, as-patterns $v$\texttt{@}$t$ where
$t$ is a variable or an as-pattern are replaced by $t$ in combination
with a local declaration for $v$.
\begin{verbatim}

> desugarLiteral :: Literal -> DsM (Either Literal ([SrcRef], [Literal]))
> desugarLiteral (Char p c) = return $ Left $ Char p c
> desugarLiteral (Int  v i) = (Left . fixType) `liftM` getValueEnv
>   where
>   fixType tyEnv
>     | typeOf tyEnv v == floatType
>     = Float (srcRefOf $ positionOfIdent v) (fromIntegral i)
>     | otherwise = Int v i
> desugarLiteral (Float p f) = return $ Left $ Float p f
> desugarLiteral (String (SrcRef [i]) cs) = return $ Right
>   (consRefs i cs, zipWith (Char . SrcRef . (:[])) [i, i + 2 ..] cs)
>   where consRefs r []     = [SrcRef [r]]
>         consRefs r (_:xs) = let r' = r + 2 in r' `seq` (SrcRef [r'] : consRefs r' xs)
> desugarLiteral (String is _) = internalError $
>   "Desugar.desugarLiteral: " ++ "wrong source ref for string "  ++ show is

> desugarList :: [SrcRef] -> (SrcRef -> b -> b -> b) -> (SrcRef -> b) -> [b] -> b
> desugarList pos cons nil xs = snd (foldr cons' nil' xs)
>   where rNil : rCs = reverse pos
>         nil'                 = (rCs , nil rNil)
>         cons' t (rC:rCs',ts) = (rCs', cons rC t ts)
>         cons' _ ([],_) = error "Desugar.desugarList.cons': empty list"

> desugarTerm :: Position -> [Decl] -> ConstrTerm -> DsM ([Decl], ConstrTerm)
> desugarTerm p ds (LiteralPattern l) =
>   desugarLiteral l >>=
>   either (return . (,) ds . LiteralPattern)
>          (\ (pos,ls) -> desugarTerm p ds $ ListPattern pos $ map LiteralPattern ls)
> desugarTerm p ds (NegativePattern _ l) =
>   desugarTerm p ds (LiteralPattern (negateLiteral l))
>   where negateLiteral (Int v i) = Int v (-i)
>         negateLiteral (Float p' f) = Float p' (-f)
>         negateLiteral _ = internalError "Desugar.negateLiteral"
> desugarTerm _ ds (VariablePattern v) = return (ds,VariablePattern v)
> desugarTerm p ds (ConstructorPattern c [t]) = do
>     tyEnv <- getValueEnv
>     liftM (if isNewtypeConstr tyEnv c then id else second (constrPat c))
>           (desugarTerm p ds t)
>   where constrPat c' t' = ConstructorPattern c' [t']
> desugarTerm p ds (ConstructorPattern c ts) =
>   liftM (second (ConstructorPattern c)) (mapAccumM (desugarTerm p) ds ts)
> desugarTerm p ds (InfixPattern t1 op t2) =
>   desugarTerm p ds (ConstructorPattern op [t1,t2])
> desugarTerm p ds (ParenPattern t) = desugarTerm p ds t
> desugarTerm p ds (TuplePattern pos ts) =
>   desugarTerm p ds (ConstructorPattern (tupleConstr ts) ts)
>   where tupleConstr ts' = addRef pos $
>                          if null ts' then qUnitId else qTupleId (length ts')
> desugarTerm p ds (ListPattern pos ts) =
>   liftM (second (desugarList pos cons nil)) (mapAccumM (desugarTerm p) ds ts)
>   where nil  p' = ConstructorPattern (addRef p' qNilId) []
>         cons p' t ts' = ConstructorPattern (addRef p' qConsId) [t,ts']
> desugarTerm p ds (AsPattern v t) =
>   liftM (desugarAs p v) (desugarTerm p ds t)
> desugarTerm p ds (LazyPattern pos t) = desugarLazy pos p ds t
> desugarTerm p ds (FunctionPattern f ts) =
>   liftM (second (FunctionPattern f)) (mapAccumM (desugarTerm p) ds ts)
> desugarTerm p ds (InfixFuncPattern t1 f t2) =
>   desugarTerm p ds (FunctionPattern f [t1,t2])
> desugarTerm p ds (RecordPattern fs _)
>   | null fs   = internalError "Desugar.desugarTerm: empty record"
>   | otherwise = do
>     tyEnv <- getValueEnv
>     case (lookupValue (fieldLabel (head fs)) tyEnv) of
>       [Label _ r _] -> desugarRecordPattern p ds (map field2Tuple fs) r
>       _             -> internalError "Desugar.desugarTerm: no label"

> desugarAs :: Position -> Ident -> ([Decl], ConstrTerm) -> ([Decl], ConstrTerm)
> desugarAs p v (ds,t) = case t of
>   VariablePattern v' -> (varDecl p v (mkVar v') : ds,t)
>   AsPattern     v' _ -> (varDecl p v (mkVar v') : ds,t)
>   _                  -> (ds, AsPattern v t)

> desugarLazy :: SrcRef -> Position -> [Decl] -> ConstrTerm -> DsM ([Decl], ConstrTerm)
> desugarLazy pos p ds t = case t of
>   VariablePattern   _ -> return (ds, t)
>   ParenPattern     t' -> desugarLazy pos p ds t'
>   AsPattern      v t' -> desugarAs p v `liftM` desugarLazy pos p ds t'
>   LazyPattern pos' t' -> desugarLazy pos' p ds t'
>   _                   -> do
>    ty <- getTypeOf t
>    v0 <- freshIdent "_#lazy" (arrowArity ty) (monoType ty) -- TODO (2011-10-12, bjp): Is this arity computation correct?
>    let v' = addPositionIdent (AST pos) v0
>    return (patDecl p{astRef=pos} t (mkVar v') : ds, VariablePattern v')

\end{verbatim}
A list of boolean guards is expanded into a nested if-then-else
expression, whereas a constraint guard is replaced by a case
expression. Note that if the guard type is \texttt{Success} only a
single guard is allowed for each equation.\footnote{This change was
introduced in version 0.8 of the Curry report.} We check for the
type \texttt{Bool} of the guard because the guard's type defaults to
\texttt{Success} if it is not restricted by the guard expression.
\begin{verbatim}

> desugarRhs :: Position -> Rhs -> DsM Rhs
> desugarRhs p rhs = do
>   tyEnv <- getValueEnv
>   e' <- desugarExpr p (expandRhs tyEnv prelFailed rhs)
>   return (SimpleRhs p e' [])

> expandRhs :: ValueEnv -> Expression -> Rhs -> Expression
> expandRhs _     _  (SimpleRhs _ e ds) = Let ds e
> expandRhs tyEnv e0 (GuardedRhs es ds) = Let ds (expandGuards tyEnv e0 es)

> expandGuards :: ValueEnv -> Expression -> [CondExpr] -> Expression
> expandGuards tyEnv e0 es
>   | booleanGuards tyEnv es = foldr mkIfThenElse e0 es
>   | otherwise              = mkCond es
>   where mkIfThenElse (CondExpr p g e) = IfThenElse (srcRefOf p) g e
>         mkCond [CondExpr _ g e] = Apply (Apply prelCond g) e
>         mkCond _ = error "Desugar.expandGuards.mkCond: non-unary list"

> booleanGuards :: ValueEnv -> [CondExpr] -> Bool
> booleanGuards _     []                    = False
> booleanGuards tyEnv (CondExpr _ g _ : es) =
>   not (null es) || typeOf tyEnv g == boolType

> desugarExpr :: Position -> Expression -> DsM Expression
> desugarExpr p (Literal l) =
>   desugarLiteral l >>=
>   either (return . Literal) (\ (pos, ls) -> desugarExpr p $ List pos $ map Literal ls)
> desugarExpr _ var@(Variable v)
>   | unqualify v == anonId = return prelUnknown
>       -- v' <- getValueEnv >>= freshIdent "_#anonfree" . polyType . flip typeOf var
>       -- desugarExpr p $ Let [ExtraVariables p [v']] $ mkVar v'
>   | otherwise             = return var
> desugarExpr _ c@(Constructor _) = return c
> desugarExpr p (Paren         e) = desugarExpr p e
> desugarExpr p (Typed       e _) = desugarExpr p e
> desugarExpr p (Tuple    pos es) =
>   apply (Constructor $ tupleConstr es) `liftM` mapM (desugarExpr p) es
>   where tupleConstr es1 = addRef pos $ if null es1 then qUnitId else qTupleId (length es1)
> desugarExpr p (List pos es) =
>   desugarList pos cons nil `liftM` mapM (desugarExpr p) es
>   where nil p'  = Constructor (addRef p' qNilId)
>         cons p' = Apply . Apply (Constructor $ addRef p' qConsId)
> desugarExpr p (ListCompr   pos e []) = desugarExpr p (List [pos,pos] [e])
> desugarExpr p (ListCompr r e (q:qs)) = desugarQual p q (ListCompr r e qs)
> desugarExpr p (EnumFrom e) =
>   Apply prelEnumFrom `liftM` desugarExpr p e
> desugarExpr p (EnumFromThen e1 e2) =
>   apply prelEnumFromThen `liftM` mapM (desugarExpr p) [e1, e2]
> desugarExpr p (EnumFromTo e1 e2) =
>   apply prelEnumFromTo `liftM` mapM (desugarExpr p) [e1, e2]
> desugarExpr p (EnumFromThenTo e1 e2 e3) =
>   apply prelEnumFromThenTo `liftM` mapM (desugarExpr p) [e1, e2, e3]
> desugarExpr p (UnaryMinus op e) = do
>   tyEnv <- getValueEnv
>   Apply (unaryMinus op (typeOf tyEnv e)) `liftM` desugarExpr p e
>   where
>   unaryMinus op1 ty
>     | op1 ==  minusId = if ty == floatType then prelNegateFloat else prelNegate
>     | op1 == fminusId = prelNegateFloat
>     | otherwise       = internalError "Desugar.unaryMinus"
> desugarExpr p (Apply (Constructor c) e) = do
>   tyEnv <- getValueEnv
>   liftM (if isNewtypeConstr tyEnv c then id else (Apply (Constructor c)))
>         (desugarExpr p e)
> desugarExpr p (Apply e1 e2) = do
>   liftM2 Apply (desugarExpr p e1) (desugarExpr p e2)
> desugarExpr p (InfixApply e1 op e2) = do
>   op' <- desugarExpr p (infixOp op)
>   e1' <- desugarExpr p e1
>   e2' <- desugarExpr p e2
>   return (Apply (Apply op' e1') e2')
> desugarExpr p (LeftSection e op) = do
>     liftM2 Apply (desugarExpr p (infixOp op)) (desugarExpr p e)
> desugarExpr p (RightSection op e) = do
>     op' <- desugarExpr p (infixOp op)
>     e' <- desugarExpr p e
>     return (Apply (Apply prelFlip op') e')
> desugarExpr p expr@(Lambda r ts e) = do
>   ty <- getTypeOf expr
>   f  <- freshIdent "_#lambda" (length ts) (polyType ty)
>   desugarExpr p $ Let [funDecl (AST r) f ts e] $ mkVar f
> desugarExpr p (Let ds e) = do
>     ds' <- desugarDeclGroup ds
>     e' <- desugarExpr p e
>     return (if null ds' then e' else Let ds' e')
> desugarExpr p (Do sts e) =
>   desugarExpr p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr r e1) e' = apply (prelBind_ r) [e1,e']
>         desugarStmt (StmtBind r t e1) e' = apply (prelBind r) [e1,Lambda r [t] e']
>         desugarStmt (StmtDecl ds) e' = Let ds e'
> desugarExpr p (IfThenElse r e1 e2 e3) = do
>     e1' <- desugarExpr p e1
>     e2' <- desugarExpr p e2
>     e3' <- desugarExpr p e3
>     return (Case r e1' [caseAlt p truePattern e2',caseAlt p falsePattern e3'])
> desugarExpr p (Case r e alts)
>   | null alts = return prelFailed
>   | otherwise = do
>         m  <- getModuleIdent
>         e' <- desugarExpr p e
>         ty <- getTypeOf e
>         v  <- freshIdent "_#case" (arrowArity ty) (monoType ty) -- TODO (2011-10-12, bjp): Is this arity computation correct?
>         alts' <- mapM desugarAltLhs alts
>         tyEnv <- getValueEnv
>         alts'' <- mapM desugarAltRhs
>                        (map (expandAlt tyEnv v) (init (tails alts')))
>         return (mkCase m v e' alts'')
>   where mkCase m1 v e1 alts1
>           | v `elem` qfv m1 alts1 = Let [varDecl p v e1] (Case r (mkVar v) alts1)
>           | otherwise = Case r e1 alts1
> desugarExpr p (RecordConstr fs)
>   | null fs = internalError "Desugar.desugarExpr: empty record construction"
>   | otherwise = do
>       let l   = fieldLabel (head fs)
>           fs' = map field2Tuple fs
>       tyEnv <- getValueEnv
>       case (lookupValue l tyEnv) of
>            [Label _ r _] -> desugarRecordConstr p r fs'
>            _  -> internalError "Desugar.desugarExpr: illegal record construction"
> desugarExpr p (RecordSelection e l) =
>   do tyEnv <- getValueEnv
>      case lookupValue l tyEnv of
>        [Label _ r _] -> desugarRecordSelection p r l e
>        _ -> internalError "Desugar.desugarExpr: illegal record selection"
> desugarExpr p (RecordUpdate fs rexpr)
>   | null fs = internalError "Desugar.desugarExpr: empty record update"
>   | otherwise = do
>       let l   = fieldLabel (head fs)
>           fs' = map field2Tuple fs
>       tyEnv <- getValueEnv
>       case (lookupValue l tyEnv) of
>            [Label _ r _] -> desugarRecordUpdate p r rexpr fs'
>            _  -> internalError "Desugar.desugarExpr: illegal record update"

\end{verbatim}
If an alternative in a case expression has boolean guards and all of
these guards return \texttt{False}, the enclosing case expression does
not fail but continues to match the remaining alternatives against the
selector expression. In order to implement this semantics, which is
compatible with Haskell, we expand an alternative with boolean guards
such that it evaluates a case expression with the remaining cases that
are compatible with the matched pattern when the guards fail.
\begin{verbatim}

> desugarAltLhs :: Alt -> DsM Alt
> desugarAltLhs (Alt p t rhs) = do
>   (ds', t') <- desugarTerm p [] t
>   return $ Alt p t' (addDecls ds' rhs)

> desugarAltRhs :: Alt -> DsM Alt
> desugarAltRhs (Alt p t rhs) = Alt p t `liftM` desugarRhs p rhs

> expandAlt :: ValueEnv -> Ident -> [Alt] -> Alt
> expandAlt tyEnv v (Alt p t rhs : alts) = caseAlt p t (expandRhs tyEnv e0 rhs)
>   where e0 = Case (srcRefOf p) (mkVar v)
>                   (filter (isCompatible t . altPattern) alts)
>         altPattern (Alt _ t1 _) = t1
> expandAlt _ _ [] = error "Desugar.expandAlt: empty list"

> isCompatible :: ConstrTerm -> ConstrTerm -> Bool
> isCompatible (VariablePattern _) _ = True
> isCompatible _ (VariablePattern _) = True
> isCompatible (AsPattern _ t1)   t2 = isCompatible t1 t2
> isCompatible t1 (AsPattern   _ t2) = isCompatible t1 t2
> isCompatible (ConstructorPattern c1 ts1) (ConstructorPattern c2 ts2) =
>   and ((c1 == c2) : zipWith isCompatible ts1 ts2)
> isCompatible (LiteralPattern l1) (LiteralPattern l2) = canon l1 == canon l2
>   where canon (Int _ i) = Int anonId i
>         canon l = l
> isCompatible _ _ = error "Desugar.isCompatible: no pattern match"

\end{verbatim}
The frontend provides several extensions of the Curry functionality, which
have to be desugared as well. This part transforms the following extensions:
\begin{itemize}
\item runction patterns
\item records
\end{itemize}
\begin{verbatim}

> desugarFunctionPatterns :: Position -> [ConstrTerm] -> Rhs -> DsM ([ConstrTerm], Rhs)
> desugarFunctionPatterns p ts rhs = do
>   (ts', its) <- elimFunctionPattern p ts
>   rhs' <- genFunctionPatternExpr its rhs
>   return (ts', rhs')

> desugarRecordDecl :: Decl -> DsM [Decl]
> desugarRecordDecl (TypeDecl p r vs (RecordType fss _)) = do
>   m <- getModuleIdent
>   tcEnv <- getTyConsEnv
>   let r' = qualifyWith m r
>   case qualLookupTC r' tcEnv of
>     [AliasType _ n (TypeRecord fs' _)] -> do
>	   let tys = concatMap (\ (ls,ty) -> replicate (length ls) ty) fss
>	       --tys' = map (elimRecordTypes tyEnv) tys
>	       rdecl = DataDecl p r vs [ConstrDecl p [] r tys]
>	       rty' = TypeConstructor r' (map TypeVariable [0 .. n-1])
>              rcts' = ForAllExist 0 n (foldr TypeArrow rty' (map snd fs'))
>	   rfuncs <- mapM (genRecordFuncs p r' rty' (map fst fs')) fs'
>	   modifyValueEnv (bindGlobalInfo (flip DataConstructor (length tys)) m r rcts')
>          return (rdecl:(concat rfuncs))
>     _ -> internalError "Desugar.desugarRecordDecl: no record"
> desugarRecordDecl decl = return [decl]

> desugarRecordPattern :: Position -> [Decl] -> [(Ident, ConstrTerm)] -> QualIdent
>                     -> DsM ([Decl], ConstrTerm)
> desugarRecordPattern p ds fs r = do
>   tcEnv <- getTyConsEnv
>   case qualLookupTC r tcEnv of
>     [AliasType _ _ (TypeRecord fs' _)] -> do
>       let ts = map (\ (l,_) -> fromMaybe (VariablePattern anonId) (lookup l fs))
>                fs'
>       desugarTerm p ds (ConstructorPattern r ts)
>     _ -> error "Desugar.desugarRecordPattern: no pattern match"

> desugarRecordConstr :: Position -> QualIdent -> [(Ident,Expression)] -> DsM Expression
> desugarRecordConstr p r fs = do
>   tcEnv <- getTyConsEnv
>   case qualLookupTC r tcEnv of
>     [AliasType _ _ (TypeRecord fs' _)] -> do
>       let cts = map (\ (l,_) -> fromMaybe (internalError "Desugar.desugarRecordConstr")
>                                 (lookup l fs)) fs'
>       desugarExpr p (foldl Apply (Constructor r) cts)
>     _ -> internalError "Desugar.desugarRecordConstr: wrong type"

> desugarRecordSelection :: Position -> QualIdent -> Ident -> Expression -> DsM Expression
> desugarRecordSelection p r l e = do
>   m <- getModuleIdent
>   desugarExpr p (Apply (Variable (qualRecSelectorId m r l)) e)

> desugarRecordUpdate :: Position -> QualIdent -> Expression -> [(Ident, Expression)] -> DsM Expression
> desugarRecordUpdate p r rexpr fs = do
>   m <- getModuleIdent
>   desugarExpr p (foldl (genRecordUpdate m r) rexpr fs)
>   where
>   genRecordUpdate m1 r1 rexpr1 (l,e) =
>     Apply (Apply (Variable (qualRecUpdateId m1 r1 l)) rexpr1) e

> elimFunctionPattern :: Position -> [ConstrTerm] -> DsM ([ConstrTerm], [(Ident,ConstrTerm)])
> elimFunctionPattern _ [] = return ([],[])
> elimFunctionPattern p (t:ts)
>   | containsFuncPat t = do
>       ty <- getTypeOf t
>       ident <- freshIdent "_#funpatt" (arrowArity ty) (monoType ty) -- TODO (2011-10-12, bjp): Is this arity computation correct?
>       (ts',its') <- elimFunctionPattern p ts
>       return ((VariablePattern ident):ts', (ident,t):its')
>   | otherwise = do
>       (ts', its') <- elimFunctionPattern p ts
>       return (t : ts', its')

> containsFuncPat :: ConstrTerm -> Bool
> containsFuncPat (ConstructorPattern _ ts) = any containsFuncPat ts
> containsFuncPat (InfixPattern    t1 _ t2) = any containsFuncPat [t1, t2]
> containsFuncPat (ParenPattern          t) = containsFuncPat t
> containsFuncPat (TuplePattern       _ ts) = any containsFuncPat ts
> containsFuncPat (ListPattern        _ ts) = any containsFuncPat ts
> containsFuncPat (AsPattern           _ t) = containsFuncPat t
> containsFuncPat (LazyPattern         _ t) = containsFuncPat t
> containsFuncPat (FunctionPattern     _ _) = True
> containsFuncPat (InfixFuncPattern  _ _ _) = True
> containsFuncPat _                         = False

> genFunctionPatternExpr :: [(Ident, ConstrTerm)] -> Rhs -> DsM Rhs
> genFunctionPatternExpr its rhs@(SimpleRhs p expr decls)
>    | null its = return rhs
>    | otherwise
>      = let ies = map (\ (i,t) -> (i, constrTerm2Expr t)) its
>	     fpexprs = map (\ (ident, expr1)
>		            -> Apply (Apply prelFuncPattEqu expr1)
>		                     (Variable (qualify ident)))
>	                   ies
>	     fpexpr =  foldl (\e1 e2 -> Apply (Apply prelConstrConj e1) e2)
>	                     (head fpexprs)
>		             (tail fpexprs)
>	     freevars = foldl getConstrTermVars [] (map snd its)
>            rhsexpr = Let [ExtraVariables p freevars]
>		           (Apply (Apply prelCond fpexpr) expr)
>        in  return (SimpleRhs p rhsexpr decls)
> genFunctionPatternExpr _ _
>    = internalError "Desugar.genFunctionPatternExpr: unexpected right-hand-side"

> constrTerm2Expr :: ConstrTerm -> Expression
> constrTerm2Expr (LiteralPattern lit)    = Literal lit
> constrTerm2Expr (VariablePattern ident) = Variable (qualify ident)
> constrTerm2Expr (ConstructorPattern qident cts)
>    = foldl (\e1 e2 -> Apply e1 e2)
>            (Constructor qident)
>            (map constrTerm2Expr cts)
> constrTerm2Expr (FunctionPattern qident cts)
>    = foldl (\e1 e2 -> Apply e1 e2)
>            (Variable qident)
>            (map constrTerm2Expr cts)
> constrTerm2Expr _
>    = internalError "Desugar.constrTerm2Expr: unexpected constructor term"

> getConstrTermVars :: [Ident] -> ConstrTerm -> [Ident]
> getConstrTermVars ids (VariablePattern ident)
>   | elem ident ids = ids
>   | otherwise      = ident : ids
> getConstrTermVars ids (ConstructorPattern _ cts)
>   = foldl getConstrTermVars ids cts
> getConstrTermVars ids (InfixPattern c1 qid c2)
>   = getConstrTermVars ids (ConstructorPattern qid [c1,c2])
> getConstrTermVars ids (ParenPattern c)
>   = getConstrTermVars ids c
> getConstrTermVars ids (TuplePattern _ cts)
>   = foldl getConstrTermVars ids cts
> getConstrTermVars ids (ListPattern _ cts)
>   = foldl getConstrTermVars ids cts
> getConstrTermVars ids (AsPattern _ c)
>   = getConstrTermVars ids c
> getConstrTermVars ids (LazyPattern _ c)
>   = getConstrTermVars ids c
> getConstrTermVars ids (FunctionPattern _ cts)
>   = foldl getConstrTermVars ids cts
> getConstrTermVars ids (InfixFuncPattern c1 qid c2)
>   = getConstrTermVars ids (FunctionPattern qid [c1,c2])
> getConstrTermVars ids _
>   = ids

> genRecordFuncs :: Position -> QualIdent -> Type -> [Ident] -> (Ident, Type) -> DsM [Decl]
> genRecordFuncs p r rty ls (l,ty) = do
>   m <- getModuleIdent
>   tcEnv <- getTyConsEnv
>   case qualLookupTC r tcEnv of
>     [AliasType _ _ (TypeRecord _ _)] -> do
>       let (selId, selFunc) = genSelectorFunc p r ls l
>           (updId, updFunc) = genUpdateFunc   p r ls l
>           selType = polyType (TypeArrow rty ty)
>           updType = polyType (TypeArrow rty $ TypeArrow ty rty)
>       modifyValueEnv (bindFun m selId 1 selType . bindFun m updId 2 updType)
>       return [selFunc, updFunc]
>     _ -> internalError "Transformations.Desugar.genRecordFuncs: wrong type"

> genSelectorFunc ::Position -> QualIdent -> [Ident] -> Ident -> (Ident, Decl)
> genSelectorFunc p r ls l =
>   let selId = recSelectorId r l
>       cpatt = ConstructorPattern r (map VariablePattern ls)
>       selLhs = FunLhs selId [cpatt]
>       selRhs = SimpleRhs p (Variable (qualify l)) []
>   in  (selId, FunctionDecl p selId [Equation p selLhs selRhs])

> genUpdateFunc :: Position -> QualIdent -> [Ident] -> Ident -> (Ident, Decl)
> genUpdateFunc p r ls l =
>   let updId = recUpdateId r l
>       ls' = replaceIdent l anonId ls
>       cpatt1 = ConstructorPattern r (map VariablePattern ls')
>       cpatt2 = VariablePattern l
>       cexpr = foldl Apply (Constructor r) (map (Variable . qualify) ls)
>       updLhs = FunLhs updId [cpatt1, cpatt2]
>       updRhs = SimpleRhs p cexpr []
>   in  (updId, FunctionDecl p updId [Equation p updLhs updRhs])

> replaceIdent :: Ident -> Ident -> [Ident] -> [Ident]
> replaceIdent _    _    []            = []
> replaceIdent what with (ident : ids)
>   | ident == what = with  : ids
>   | otherwise     = ident : (replaceIdent what with ids)

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

> desugarQual :: Position -> Statement -> Expression -> DsM Expression
> desugarQual p (StmtExpr       pos b) e =
>   desugarExpr p (IfThenElse pos b e (List [pos] []))
> desugarQual p (StmtDecl          ds) e = desugarExpr p (Let ds e)
> desugarQual p (StmtBind refBind t l) e
>   | isVarPattern t = desugarExpr p (qualExpr t e l)
>   | otherwise      = do
>       tty <- getTypeOf t
>       v0  <- freshIdent "_#var" (arrowArity tty) (monoType tty) -- TODO (2011-10-12, bjp): Is this arity computation correct?
>       ety <- getTypeOf e
>       l0  <- freshIdent "_#var" (arrowArity ety) (monoType ety) -- TODO (2011-10-12, bjp): Is this arity computation correct?
>       let v  = addRefId refBind v0
>           l' = addRefId refBind l0
>       desugarExpr p (apply (prelFoldr refBind)
>                            [foldFunct v l' e,List [refBind] [],l])
>   where
>     qualExpr v (ListCompr _ e1 []) l1
>       = apply (prelMap refBind) [Lambda refBind [v] e1,l1]
>     qualExpr v e1 l1 = apply (prelConcatMap refBind) [Lambda refBind [v] e1,l1]

>     foldFunct v l1 e1 =
>           Lambda refBind (map VariablePattern [v,l1])
>             (Case refBind (mkVar v)
>                   [caseAlt {-refBind-} p t (append e1 (mkVar l1)),
>                    caseAlt {-refBind-} p (VariablePattern v) (mkVar l1)])
>
>     append (ListCompr _ e1 []) l1 = apply (Constructor $ addRef refBind $ qConsId) [e1,l1]
>     append e1 l1 = apply (prelAppend refBind) [e1,l1]

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

> prelFuncPattEqu :: Expression
> prelFuncPattEqu = Variable $ preludeIdent "=:<="

> prelConstrConj :: Expression
> prelConstrConj = Variable $ preludeIdent "&"

> prel :: String -> SrcRef -> Expression
> prel s r = Variable $ addRef r $ preludeIdent s

> truePattern :: ConstrTerm
> truePattern = ConstructorPattern qTrueId []

> falsePattern :: ConstrTerm
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
>   _ -> internalError $ "Transformations.Desugar.isNewtypeConstr: " ++ show c

> isVarPattern :: ConstrTerm -> Bool
> isVarPattern (VariablePattern _) = True
> isVarPattern (ParenPattern    t) = isVarPattern t
> isVarPattern (AsPattern     _ t) = isVarPattern t
> isVarPattern (LazyPattern   _ _) = True
> isVarPattern _                   = False

> funDecl :: Position -> Ident -> [ConstrTerm] -> Expression -> Decl
> funDecl p f ts e = FunctionDecl p f
>   [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> patDecl :: Position -> ConstrTerm -> Expression -> Decl
> patDecl p t e = PatternDecl p t (SimpleRhs p e [])

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p = patDecl p . VariablePattern

> addDecls :: [Decl] -> Rhs -> Rhs
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

> caseAlt :: Position -> ConstrTerm -> Expression -> Alt
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> apply :: Expression -> [Expression] -> Expression
> apply = foldl Apply

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

\end{verbatim}
