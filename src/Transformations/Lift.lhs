% $Id: Lift.lhs,v 1.23 2004/02/13 14:02:54 wlux Exp $
%
% Copyright (c) 2001-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Lift.lhs}
\section{Lifting Declarations}
After desugaring and simplifying the code, the compiler lifts all local
function declarations to the top-level keeping only local variable
declarations. The algorithm used here is similar to
Johnsson's~\cite{Johnsson87:Thesis} (see also chapter 6
of~\cite{PeytonJonesLester92:Book}). It consists of two phases, first we
abstract each local function declaration, adding its free variables as
initial parameters and update all calls to take these variables into account.
Then all local function declarations are collected and lifted to the
top-level.
\begin{verbatim}

> module Transformations.Lift (lift) where

> import           Control.Monad              (liftM, liftM2)
> import qualified Control.Monad.State as S   (State, runState, gets, modify)
> import           Data.List
> import qualified Data.Map            as Map (Map, empty, insert, lookup)
> import qualified Data.Set            as Set (toList, fromList, unions)

> import Curry.Base.Ident
> import Curry.Syntax

> import Base.Expr
> import Base.Messages (internalError)
> import Base.SCC
> import Base.Types

> import Env.Value

> lift :: ValueEnv -> Module -> (Module, ValueEnv)
> lift tyEnv (Module ps m es is ds) = (lifted, valueEnv s')
>   where
>   (ds', s') = S.runState (mapM (abstractDecl "" []) ds) initState
>   initState = LiftState m tyEnv Map.empty
>   lifted    = Module ps m es is $ concatMap liftFunDecl ds'

\end{verbatim}
\paragraph{Abstraction}
Besides adding the free variables to every (local) function, the
abstraction pass also has to update the type environment in order to
reflect the new types of the expanded functions. As usual we use a
state monad transformer in order to pass the type environment
through. The environment constructed in the abstraction phase maps
each local function declaration onto its replacement expression,
i.e. the function applied to its free variables.
\begin{verbatim}

> type AbstractEnv = Map.Map Ident Expression

> data LiftState = LiftState
>   { moduleIdent :: ModuleIdent
>   , valueEnv    :: ValueEnv
>   , abstractEnv :: AbstractEnv
>   }

> type LiftM a = S.State LiftState a

> getModuleIdent :: LiftM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> getValueEnv :: LiftM ValueEnv
> getValueEnv = S.gets valueEnv

> modifyValueEnv :: (ValueEnv -> ValueEnv) -> LiftM ()
> modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

> getAbstractEnv :: LiftM AbstractEnv
> getAbstractEnv = S.gets abstractEnv

> withLocalAbstractEnv :: AbstractEnv -> LiftM a -> LiftM a
> withLocalAbstractEnv ae act = do
>   old <- getAbstractEnv
>   S.modify $ \ s -> s { abstractEnv = ae }
>   res <- act
>   S.modify $ \ s -> s { abstractEnv = old }
>   return res

> abstractDecl :: String -> [Ident] -> Decl -> LiftM Decl
> abstractDecl _   lvs (FunctionDecl p f eqs) =
>   FunctionDecl p f `liftM` mapM (abstractEquation lvs) eqs
> abstractDecl pre lvs (PatternDecl  p t rhs) =
>   PatternDecl p t `liftM` abstractRhs pre lvs rhs
> abstractDecl _   _   d                      = return d

> abstractEquation :: [Ident] -> Equation -> LiftM Equation
> abstractEquation lvs (Equation p lhs@(FunLhs f ts) rhs) =
>   Equation p lhs `liftM` abstractRhs (idName f ++ ".") (lvs ++ bv ts) rhs
> abstractEquation _ _ = error "Lift.abstractEquation: no pattern match"

> abstractRhs :: String -> [Ident] -> Rhs -> LiftM Rhs
> abstractRhs pre lvs (SimpleRhs p e _) =
>   flip (SimpleRhs p) [] `liftM` abstractExpr pre lvs e
> abstractRhs _ _ _ = error "Lift.abstractRhs: no pattern match"

\end{verbatim}
Within a declaration group we have to split the list of declarations
into the function and value declarations. Only the function
declarations are affected by the abstraction algorithm; the value
declarations are left unchanged except for abstracting their right
hand sides.

The abstraction of a recursive declaration group is complicated by the
fact that not all functions need to call each in a recursive
declaration group. E.g., in the following example neither g nor h
call each other.
\begin{verbatim}
  f = g True
    where x = f 1
          f z = y + z
          y = g False
          g z = if z then x else 0
\end{verbatim}
Because of this fact, f and g can be abstracted separately by adding
only \texttt{y} to \texttt{f} and \texttt{x} to \texttt{g}. On the
other hand, in the following example
\begin{verbatim}
  f x y = g 4
    where g p = h p + x
          h q = k + y + q
          k = g x
\end{verbatim}
the local function \texttt{g} uses \texttt{h}, so the free variables
of \texttt{h} have to be added to \texttt{g} as well. However, because
\texttt{h} does not call \texttt{g} it is sufficient to add only
\texttt{k} and \texttt{y} (and not \texttt{x}) to its definition. We
handle this by computing the dependency graph between the functions
and splitting this graph into its strongly connected components. Each
component is then processed separately, adding the free variables in
the group to its functions.

We have to be careful with local declarations within desugared case
expressions. If some of the cases have guards, e.g.,
\begin{verbatim}
  case e of
    x | x < 1 -> 1
    x -> let double y = y * y in double x
\end{verbatim}
the desugarer at present may duplicate code. While there is no problem
with local variable declaration being duplicated, we must avoid to
lift local function declarations more than once. Therefore
\texttt{abstractFunDecls} transforms only those function declarations
that have not been lifted and discards the other declarations. Note
that it is easy to check whether a function has been lifted by
checking whether an entry for its untransformed name is still present
in the type environment.
\begin{verbatim}

> abstractDeclGroup :: String -> [Ident]
>                   -> [Decl] -> Expression -> LiftM Expression
> abstractDeclGroup pre lvs ds e = do
>   m <- getModuleIdent
>   abstractFunDecls pre (lvs ++ bv vds) (scc bv (qfv m) fds) vds e
>   where (fds,vds) = partition isFunDecl ds

> abstractFunDecls :: String -> [Ident]
>                  -> [[Decl]] -> [Decl] -> Expression
>                  -> LiftM Expression
> abstractFunDecls pre lvs [] vds e = do
>   vds' <- mapM (abstractDecl pre lvs) vds
>   e' <- abstractExpr pre lvs e
>   return (Let vds' e')
> abstractFunDecls pre lvs (fds:fdss) vds e = do
>   m   <- getModuleIdent
>   env <- getAbstractEnv
>   let fs     = bv fds
>       fvs    = filter (`elem` lvs) (Set.toList fvsRhs)
>       env'   = foldr (bindF (map mkVar fvs)) env fs
>       fvsRhs = Set.unions
>         [Set.fromList (maybe [v] (qfv m) (Map.lookup v env)) | v <- qfv m fds]
>       bindF fvs' f = Map.insert f (apply (mkFun m pre f) fvs')
>       isLifted tyEnv f = null $ lookupValue f tyEnv
>   fs' <- liftM (\tyEnv -> filter (not . isLifted tyEnv) fs) getValueEnv
>   modifyValueEnv $ abstractFunTypes m pre fvs fs'
>   (fds',e') <- withLocalAbstractEnv env' $ do
>     fds'' <- mapM (abstractFunDecl pre fvs lvs)
>                [d | d <- fds, any (`elem` fs') (bv d)]
>     e'' <- abstractFunDecls pre lvs fdss vds e
>     return (fds'',e'')
>   return (Let fds' e')

> abstractFunTypes :: ModuleIdent -> String -> [Ident] -> [Ident]
>                  -> ValueEnv -> ValueEnv
> abstractFunTypes m pre fvs fs tyEnv = foldr abstractFunType tyEnv fs
>   where tys = map (varType tyEnv) fvs
>         abstractFunType f tyEnv' =
>           qualBindFun m (liftIdent pre f)
>                         (length fvs + varArity tyEnv' f) -- (arrowArity ty)
>                         (polyType ty)
>                         (unbindFun f tyEnv')
>           where ty = foldr TypeArrow (varType tyEnv' f) tys

> abstractFunDecl :: String -> [Ident] -> [Ident] -> Decl -> LiftM Decl
> abstractFunDecl pre fvs lvs (FunctionDecl p f eqs) =
>   abstractDecl pre lvs (FunctionDecl p f' (map (addVars f') eqs))
>   where
>   f' = liftIdent pre f
>   addVars f1 (Equation p1 (FunLhs _ ts) rhs) =
>           Equation p1 (FunLhs f1 (map VariablePattern fvs ++ ts)) rhs
>   addVars _ _ = error "Lift.abstractFunDecl.addVars: no pattern match"
> abstractFunDecl pre _   _  (ForeignDecl p cc ie f ty) =
>   return $ ForeignDecl p cc ie (liftIdent pre f) ty
> abstractFunDecl _ _ _ _ = error "Lift.abstractFunDecl: no pattern match"

> abstractExpr :: String -> [Ident] -> Expression -> LiftM Expression
> abstractExpr _   _   l@(Literal      _) = return l
> abstractExpr pre lvs var@(Variable   v)
>   | isQualified v = return var
>   | otherwise     = do
>     env <- getAbstractEnv
>     case Map.lookup (unqualify v) env of
>       Nothing -> return var
>       Just v' -> abstractExpr pre lvs v'
> abstractExpr _   _   c@(Constructor  _) = return c
> abstractExpr pre lvs (Apply      e1 e2) =
>   liftM2 Apply (abstractExpr pre lvs e1) (abstractExpr pre lvs e2)
> abstractExpr pre lvs (Let         ds e) = abstractDeclGroup pre lvs ds e
> abstractExpr pre lvs (Case r ct e alts) =
>   liftM2 (Case r ct) (abstractExpr pre lvs e)
>                      (mapM (abstractAlt pre lvs) alts)
> abstractExpr pre lvs (Typed       e ty) = flip Typed ty `liftM`
>                                           abstractExpr pre lvs e
> abstractExpr _   _   _                  = internalError "Lift.abstractExpr"

> abstractAlt :: String -> [Ident] -> Alt -> LiftM Alt
> abstractAlt pre lvs (Alt p t rhs) =
>   Alt p t `liftM` abstractRhs pre (lvs ++ bv t) rhs

\end{verbatim}
\paragraph{Lifting}
After the abstraction pass, all local function declarations are lifted
to the top-level.
\begin{verbatim}

> liftFunDecl :: Decl -> [Decl]
> liftFunDecl (FunctionDecl p f eqs) = (FunctionDecl p f eqs' : concat dss')
>   where (eqs', dss') = unzip $ map liftEquation eqs
> liftFunDecl d = [d]

> liftVarDecl :: Decl -> (Decl, [Decl])
> liftVarDecl (PatternDecl   p t rhs) = (PatternDecl p t rhs', ds')
>   where (rhs', ds') = liftRhs rhs
> liftVarDecl ex@(FreeDecl _ _) = (ex, [])
> liftVarDecl _ = error "Lift.liftVarDecl: no pattern match"

> liftEquation :: Equation -> (Equation, [Decl])
> liftEquation (Equation p lhs rhs) = (Equation p lhs rhs', ds')
>   where (rhs', ds') = liftRhs rhs

> liftRhs :: Rhs -> (Rhs, [Decl])
> liftRhs (SimpleRhs p e _) = (SimpleRhs p e' [], ds')
>   where (e', ds') = liftExpr e
> liftRhs _ = error "Lift.liftRhs: no pattern match"

> liftDeclGroup :: [Decl] -> ([Decl],[Decl])
> liftDeclGroup ds = (vds', concat $ map liftFunDecl fds ++ dss')
>   where (fds , vds ) = partition isFunDecl ds
>         (vds', dss') = unzip $ map liftVarDecl vds

> liftExpr :: Expression -> (Expression, [Decl])
> liftExpr l@(Literal      _) = (l, [])
> liftExpr v@(Variable     _) = (v, [])
> liftExpr c@(Constructor  _) = (c, [])
> liftExpr (Apply      e1 e2) = (Apply e1' e2', ds' ++ ds'')
>   where (e1', ds' ) = liftExpr e1
>         (e2', ds'') = liftExpr e2
> liftExpr (Let         ds e) = (mkLet ds' e', ds'' ++ ds''')
>   where (ds', ds'' ) = liftDeclGroup ds
>         (e' , ds''') = liftExpr e
>         mkLet ds1 e1 = if null ds1 then e1 else Let ds1 e1
> liftExpr (Case r ct e alts) = (Case r ct e' alts', concat $ ds' : dss')
>   where (e'   ,ds' ) = liftExpr e
>         (alts',dss') = unzip $ map liftAlt alts
> liftExpr (Typed       e ty) = (Typed e' ty, ds) where (e', ds) = liftExpr e
> liftExpr _ = internalError "Lift.liftExpr"

> liftAlt :: Alt -> (Alt, [Decl])
> liftAlt (Alt p t rhs) = (Alt p t rhs', ds') where (rhs', ds') = liftRhs rhs

\end{verbatim}
\paragraph{Auxiliary definitions}
\begin{verbatim}

> isFunDecl :: Decl -> Bool
> isFunDecl (FunctionDecl     _ _ _) = True
> isFunDecl (ForeignDecl  _ _ _ _ _) = True
> isFunDecl _                        = False

> mkFun :: ModuleIdent -> String -> Ident -> Expression
> mkFun m pre f = Variable $ qualifyWith m $ liftIdent pre f

> mkVar :: Ident -> Expression
> mkVar v = Variable $ qualify v

> apply :: Expression -> [Expression] -> Expression
> apply = foldl Apply

> varArity :: ValueEnv -> Ident -> Int
> varArity tyEnv v = case lookupValue v tyEnv of
>   [Value _ a _] -> a
>   _ -> internalError $ "Lift.varArity: " ++ show v

> varType :: ValueEnv -> Ident -> Type
> varType tyEnv v = case lookupValue v tyEnv of
>   [Value _ _ (ForAll _ ty)] -> ty
>   _ -> internalError $ "Lift.varType: " ++ show v

> liftIdent :: String -> Ident -> Ident
> liftIdent prefix x = renameIdent (mkIdent $ prefix ++ showIdent x)
>                    $ idUnique x

\end{verbatim}
