
% $Id: SyntaxCheck.lhs,v 1.53 2004/02/15 22:10:37 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{SyntaxCheck.lhs}
\section{Syntax Checks}
After the type declarations have been checked, the compiler performs a
syntax check on the remaining declarations. This check disambiguates
nullary data constructors and variables which -- in contrast to
Haskell -- is not possible on purely syntactic criteria. In addition,
this pass checks for undefined as well as ambiguous variables and
constructors. In order to allow lifting of local definitions in
later phases, all local variables are renamed by adding a unique
key.\footnote{Actually, all variables defined in the same scope share
the same key.} Finally, all (adjacent) equations of a function are
merged into a single definition.
\begin{verbatim}

> module SyntaxCheck(syntaxCheck) where
> import Base
> import Env
> import NestEnv
> import List
> import Maybe
> import Monad
> import Combined
> import Utils

\end{verbatim}
The syntax checking proceeds as follows. First, the compiler extracts
information about all imported values and data constructors from the
imported (type) environments. Next, the data constructors defined in
the current module are entered into this environment. Finally, all
declarations are checked within the resulting environment. In
addition, this process will also rename the local variables.
\begin{verbatim}

> syntaxCheck :: Bool -> ModuleIdent -> ImportEnv -> ArityEnv -> ValueEnv 
>                -> [Decl] -> [Decl]
> syntaxCheck withExt m iEnv aEnv tyEnv ds =
>   case linear (concatMap constrs tds) of
>     Linear -> tds ++ run (checkModule withExt m env vds)
>     NonLinear (PIdent p c) -> errorAt p (duplicateData c)
>   where (tds,vds) = partition isTypeDecl ds
>         env = foldr (bindConstrs m) 
>	              (globalEnv (fmap (renameInfo iEnv aEnv) tyEnv)) 
>	              tds

> --syntaxCheckGoal :: Bool -> ValueEnv -> Goal -> Goal
> --syntaxCheckGoal withExt tyEnv g =
> --  run (checkGoal withExt (mkMIdent []) (globalEnv (fmap renameInfo tyEnv)) g)

\end{verbatim}
A global state transformer is used for generating fresh integer keys
by which the variables get renamed.
\begin{verbatim}

> type RenameState a = StateT Int Id a

> run :: RenameState a -> a
> run m = runSt m (globalKey + 1)

> newId :: RenameState Int
> newId = updateSt (1 +)

\end{verbatim}
\ToDo{Probably the state transformer should use an \texttt{Integer} 
counter.}

A nested environment is used for recording information about the data
constructors and variables in the module. For every data constructor
its arity is saved. This is used for checking that all constructor
applications in patterns are saturated. For local variables the
environment records the new name of the variable after renaming.
Global variables are recorded with qualified identifiers in order
to distinguish multiply declared entities.

\em{Note:} the function \texttt{qualLookupVar} has been extended to
allow the usage of the qualified list constructor \texttt{(prelude.:)}.
\begin{verbatim}

> type RenameEnv = NestEnv RenameInfo
> data RenameInfo = Constr Int 
>                 | GlobalVar Int QualIdent 
>                 | LocalVar Int Ident deriving (Eq,Show)

> globalKey :: Int
> globalKey = uniqueId (mkIdent "")

> renameInfo :: ImportEnv -> ArityEnv -> ValueInfo -> RenameInfo
> renameInfo iEnv aEnv (DataConstructor _ (ForAllExist _ _ ty)) 
>    = Constr (arrowArity ty)
> renameInfo iEnv aEnv (NewtypeConstructor _ _) 
>    = Constr 1
> renameInfo iEnv aEnv (Value qid _)
>    = let (mmid, id) = splitQualIdent qid
>          qid' = maybe qid 
>	                (\mid -> maybe qid 
>		                       (\mid' -> qualifyWith mid' id)
>				       (lookupAlias mid iEnv))
>		        mmid
>      in case (qualLookupArity qid' aEnv) of
>           [ArityInfo _ arity] -> GlobalVar arity qid
>           _ -> internalError "renameInfo: unexpected result"

> bindConstrs :: ModuleIdent -> Decl -> RenameEnv -> RenameEnv
> bindConstrs m (DataDecl _ tc _ cs) env = foldr (bindConstr m) env cs
> bindConstrs m (NewtypeDecl _ tc _ nc) env = bindNewConstr m nc env
> bindConstrs _ _ env = env

> bindConstr :: ModuleIdent -> ConstrDecl -> RenameEnv -> RenameEnv
> bindConstr m (ConstrDecl _ _ c tys) = bindGlobal m c (Constr (length tys))
> bindConstr m (ConOpDecl _ _ _ op _) = bindGlobal m op (Constr 2)

> bindNewConstr :: ModuleIdent -> NewConstrDecl -> RenameEnv -> RenameEnv
> bindNewConstr m (NewConstrDecl _ _ c _) = bindGlobal m c (Constr 1)

> bindFuncDecl :: ModuleIdent -> Decl -> RenameEnv -> RenameEnv
> bindFuncDecl m (FunctionDecl _ id equs) env
>    | null equs = internalError "bindFuncDecl: missing equations"
>    | otherwise = let (_,ts) = getFlatLhs (head equs)
>		   in  bindGlobal m 
>	                          id 
>			          (GlobalVar (length ts) (qualifyWith m id))
>	                          env
> bindFuncDecl m (ExternalDecl _ _ _ id texpr) env
>    = bindGlobal m id (GlobalVar (typeArity texpr) (qualifyWith m id)) env
> bindFuncDecl m (TypeSig _ ids texpr) env
>    = foldr bindTS env (map (qualifyWith m) ids)
>  where
>  bindTS qid env 
>     | null (qualLookupVar qid env)
>       = bindGlobal m (unqualify qid) (GlobalVar (typeArity texpr) qid) env
>     | otherwise
>       = env
> bindFuncDecl _ _ env = env

> bindVarDecl :: Decl -> RenameEnv -> RenameEnv
> bindVarDecl (FunctionDecl _ id equs) env
>    | null equs 
>      = internalError "bindFuncDecl: missing equations"
>    | otherwise 
>      = let (_,ts) = getFlatLhs (head equs)
>	 in  bindLocal (unRenameIdent id) (LocalVar (length ts) id) env
> bindVarDecl (PatternDecl p t _) env
>    = foldr bindVar env (map (PIdent p) (bv t))
> bindVarDecl (ExtraVariables p vs) env
>    = foldr bindVar env (map (PIdent p) vs) 
> bindVarDecl _ env = env

> --bindFunc :: ModuleIdent -> PIdent -> RenameEnv -> RenameEnv
> --bindFunc m (PIdent p f) = bindGlobal m f (GlobalVar (qualifyWith m f))

> bindVar :: PIdent -> RenameEnv -> RenameEnv
> bindVar (PIdent p v) env
>   | v' == anonId = env
>   | otherwise = bindLocal v' (LocalVar 0 v) env
>   where v' = unRenameIdent v

> bindGlobal :: ModuleIdent -> Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindGlobal m c r = bindNestEnv c r . qualBindNestEnv (qualifyWith m c) r

> bindLocal :: Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindLocal f r = bindNestEnv f r

> lookupVar :: Ident -> RenameEnv -> [RenameInfo]
> lookupVar v env = lookupNestEnv v env ++! lookupTupleConstr v

> qualLookupVar :: QualIdent -> RenameEnv -> [RenameInfo]
> qualLookupVar v env =
>   qualLookupNestEnv v env
>   ++! qualLookupListCons v env
>   ++! lookupTupleConstr (unqualify v)

> qualLookupListCons :: QualIdent -> RenameEnv -> [RenameInfo]
> qualLookupListCons v env
>    | (isJust mmid) && ((fromJust mmid) == preludeMIdent) && (ident == consId)
>       = qualLookupNestEnv (qualify ident) env
>    | otherwise = []
>  where (mmid, ident) = splitQualIdent v

> lookupTupleConstr :: Ident -> [RenameInfo]
> lookupTupleConstr v
>   | isTupleId v = [Constr (tupleArity v)]
>   | otherwise = []

\end{verbatim}
When a module is checked, the global declaration group is checked. The
resulting renaming environment can be discarded. The same is true for
a goal. Note that all declarations in the goal must be considered as
local declarations.
\begin{verbatim}

> checkModule :: Bool -> ModuleIdent -> RenameEnv -> [Decl] -> RenameState [Decl]
> checkModule withExt m env ds = liftM snd (checkTopDecls withExt m env ds)

> checkTopDecls :: Bool -> ModuleIdent -> RenameEnv -> [Decl]
>               -> RenameState (RenameEnv,[Decl])
> checkTopDecls withExt m env ds = 
>   checkDeclGroup (bindFuncDecl m) withExt m globalKey env ds

> --checkGoal :: Bool -> ModuleIdent -> RenameEnv -> Goal -> RenameState Goal
> --checkGoal withExt m env (Goal p e ds) =
> --  do
> --    (env',ds') <- checkLocalDecls withExt m env ds
> --    e' <- checkExpr withExt p m env' e
> --    return (Goal p e' ds')

\end{verbatim}
Each declaration group opens a new scope and uses a distinct key
for renaming the variables in this scope. In a declaration group,
first the left hand sides of all declarations are checked, next the
compiler checks that there is a definition for every type signature
and evaluation annotation in this group. Finally, the right hand sides
are checked and adjacent equations for the same function are merged
into a single definition.

The function \texttt{checkDeclLhs} also handles the case where a
pattern declaration is recognized as a function declaration by the
parser. This happens, e.g., for the declaration \verb|where Just x = y|
because the parser cannot distinguish nullary constructors and
functions. Note that pattern declarations are not allowed on the
top-level.
\begin{verbatim}

> checkLocalDecls :: Bool -> ModuleIdent -> RenameEnv -> [Decl] 
>                  -> RenameState (RenameEnv,[Decl])
> checkLocalDecls withExt m env ds =
>   newId >>= \k -> checkDeclGroup bindVarDecl withExt m k (nestEnv env) ds

> checkDeclGroup :: (Decl -> RenameEnv -> RenameEnv) -> Bool -> ModuleIdent
>                 -> Int -> RenameEnv -> [Decl] 
>                 -> RenameState (RenameEnv,[Decl])
> checkDeclGroup bindDecl withExt m k env ds =
>   mapM (checkDeclLhs withExt k m env) ds' >>=
>   checkDecls bindDecl withExt m env . joinEquations
>  where ds' = sortFuncDecls ds

> checkDeclLhs :: Bool -> Int -> ModuleIdent -> RenameEnv -> Decl -> RenameState Decl
> checkDeclLhs withExt k _ _ (InfixDecl p fix pr ops) =
>   return (InfixDecl p fix pr (map (flip renameIdent k) ops))
> checkDeclLhs withExt k _ env (TypeSig p vs ty) =
>   return (TypeSig p (map (checkVar "type signature" k p env) vs) ty)
> checkDeclLhs withExt k _ env (EvalAnnot p fs ev) =
>   return (EvalAnnot p (map (checkVar "evaluation annotation" k p env) fs) ev)
> checkDeclLhs withExt k m env (FunctionDecl p _ eqs) = 
>   checkEquationLhs withExt k m env p eqs
> checkDeclLhs withExt k _ env (ExternalDecl p cc ie f ty) =
>   return (ExternalDecl p cc ie (checkVar "external declaration" k p env f) ty)
> checkDeclLhs withExt k _ env (FlatExternalDecl p fs) =
>   return (FlatExternalDecl p
>             (map (checkVar "external declaration" k p env) fs))
> checkDeclLhs withExt k m env (PatternDecl p t rhs) =
>   do
>     t' <- checkConstrTerm withExt k p m env t
>     return (PatternDecl p t' rhs)
> checkDeclLhs withExt k _ env (ExtraVariables p vs) =
>   return (ExtraVariables p
>             (map (checkVar "free variables declaration" k p env) vs))
> checkDeclLhs _ _ _ _ d = return d

> checkEquationLhs :: Bool -> Int -> ModuleIdent -> RenameEnv -> Position 
>	           -> [Equation] -> RenameState Decl
> checkEquationLhs withExt k m env p [Equation p' lhs rhs] =
>   either (return . funDecl) (checkDeclLhs withExt k m env . patDecl)
>          (checkEqLhs k env p' lhs)
>   where funDecl (f,lhs) = FunctionDecl p f [Equation p' lhs rhs]
>         patDecl t
>           | k == globalKey = errorAt p noToplevelPattern
>           | otherwise = PatternDecl p' t rhs
> checkEquationLhs _ _ _ _ _ _ = internalError "checkEquationLhs"

> checkEqLhs :: Int -> RenameEnv -> Position -> Lhs
>            -> Either (Ident,Lhs) ConstrTerm
> checkEqLhs k env _ (FunLhs f ts)
>   | isDataConstr f env = Right (ConstructorPattern (qualify f) ts)
>   | otherwise = Left (f',FunLhs f' ts)
>   where f' = renameIdent f k
> checkEqLhs k env _ (OpLhs t1 op t2)
>   | isDataConstr op env = checkOpLhs k env (infixPattern t1 (qualify op)) t2
>   | otherwise = Left (op',OpLhs t1 op' t2)
>   where op' = renameIdent op k
>         infixPattern (InfixPattern t1 op1 t2) op2 t3 =
>           InfixPattern t1 op1 (infixPattern t2 op2 t3)
>         infixPattern t1 op t2 = InfixPattern t1 op t2
> checkEqLhs k env p (ApLhs lhs ts) =
>   case checkEqLhs k env p lhs of
>     Left (f',lhs') -> Left (f',ApLhs lhs' ts)
>     Right _ -> errorAt p $ nonVariable "curried definition" f
>   where (f,_) = flatLhs lhs

> checkOpLhs :: Int -> RenameEnv -> (ConstrTerm -> ConstrTerm) -> ConstrTerm
>            -> Either (Ident,Lhs) ConstrTerm
> checkOpLhs k env f (InfixPattern t1 op t2)
>   | isJust m || isDataConstr op' env =
>       checkOpLhs k env (f . InfixPattern t1 op) t2
>   | otherwise = Left (op'',OpLhs (f t1) op'' t2)
>   where (m,op') = splitQualIdent op
>         op'' = renameIdent op' k
> checkOpLhs _ _ f t = Right (f t)

> checkVar :: String -> Int -> Position -> RenameEnv -> Ident -> Ident
> checkVar what k p env v
>   | isDataConstr v env = errorAt p (nonVariable what v)
>   | otherwise = renameIdent v k


> checkDecls :: (Decl -> RenameEnv -> RenameEnv) -> Bool -> ModuleIdent
>	        -> RenameEnv -> [Decl] -> RenameState (RenameEnv,[Decl])
> checkDecls bindDecl withExt m env ds = --bindVar withExt m env ds =
>   case linear bvs of
>     Linear ->
>       case linear tys of
>         Linear ->
>           case linear evs of
>             Linear ->
>               case filter (`notElem` tys) fs' of
>                 [] -> liftM ((,) env') 
>		              (mapM (checkDeclRhs withExt bvs m env'') ds)
>                 PIdent p f : _ -> errorAt p (noTypeSig f)
>             NonLinear (PIdent p v) -> errorAt p (duplicateEvalAnnot v)
>         NonLinear (PIdent p v) -> errorAt p (duplicateTypeSig v)
>     NonLinear (PIdent p v) -> errorAt p (duplicateDefinition v)
>   where vds = filter isValueDecl ds
>	  tds = filter isTypeSig ds
>         bvs = concat (map vars vds)
>         tys = concat (map vars tds)
>         evs = concat (map vars (filter isEvalAnnot ds))
>         fs' = [PIdent p f | FlatExternalDecl p fs <- ds, f <- fs]
>         env' = foldr bindDecl env vds --foldr bindVar env bvs
>         env'' = foldr bindDecl env' tds

> checkDeclRhs :: Bool -> [PIdent] -> ModuleIdent -> RenameEnv -> Decl 
>              -> RenameState Decl
> checkDeclRhs withExt bvs _ _ (TypeSig p vs ty) =
>   return (TypeSig p (map (checkLocalVar bvs p) vs) ty)
> checkDeclRhs withExt bvs _ _ (EvalAnnot p vs ev) =
>   return (EvalAnnot p (map (checkLocalVar bvs p) vs) ev)
> checkDeclRhs withExt _ m env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (checkEquation withExt m env) eqs)
> checkDeclRhs withExt _ m env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (checkRhs withExt m env rhs)
> checkDeclRhs _ _ _ _ d = return d

> checkLocalVar :: [PIdent] -> Position -> Ident -> Ident
> checkLocalVar bvs p v
>   | PIdent p v `elem` bvs = v
>   | otherwise = errorAt p (noBody v)

> joinEquations :: [Decl] -> [Decl]
> joinEquations [] = []
> joinEquations (FunctionDecl p f eqs : FunctionDecl p' f' [eq] : ds)
>   | f == f' =
>       if arity (head eqs) == arity eq then
>         joinEquations (FunctionDecl p f (eqs ++ [eq]) : ds)
>       else
>         errorAt p' (differentArity f)
>   where arity (Equation _ lhs _) = length $ snd $ flatLhs lhs
> joinEquations (d : ds) = d : joinEquations ds

> checkEquation :: Bool -> ModuleIdent -> RenameEnv -> Equation -> RenameState Equation
> checkEquation withExt m env (Equation p lhs rhs) =
>   do
>     (env',lhs') <- checkLhs withExt p m env lhs
>     rhs' <- checkRhs withExt m env' rhs
>     return (Equation p lhs' rhs')

> checkLhs :: Bool -> Position -> ModuleIdent -> RenameEnv -> Lhs 
>             -> RenameState (RenameEnv,Lhs)
> checkLhs withExt p m env lhs =
>   newId >>= \k ->
>   checkLhsTerm withExt k p m env lhs >>=
>   return . checkConstrTerms withExt p (nestEnv env)

> checkLhsTerm :: Bool -> Int -> Position -> ModuleIdent -> RenameEnv -> Lhs 
>                 -> RenameState Lhs
> checkLhsTerm withExt k p m env (FunLhs f ts) =
>   do
>     ts' <- mapM (checkConstrTerm withExt k p m env) ts
>     return (FunLhs f ts')
> checkLhsTerm withExt k p m env (OpLhs t1 op t2) =
>   do
>     t1' <- checkConstrTerm withExt k p m env t1
>     t2' <- checkConstrTerm withExt k p m env t2
>     return (OpLhs t1' op t2')
> checkLhsTerm withExt k p m env (ApLhs lhs ts) =
>   do
>     lhs' <- checkLhsTerm withExt k p m env lhs
>     ts' <- mapM (checkConstrTerm withExt k p m env) ts
>     return (ApLhs lhs' ts')

> checkArgs :: Bool -> Position -> ModuleIdent -> RenameEnv -> [ConstrTerm]
>           -> RenameState (RenameEnv,[ConstrTerm])
> checkArgs withExt p m env ts =
>   newId >>= \k ->
>   mapM (checkConstrTerm withExt k p m env) ts >>=
>   return . checkConstrTerms withExt p (nestEnv env)

> checkConstrTerms :: QuantExpr t => Bool -> Position -> RenameEnv -> t
>                  -> (RenameEnv,t)
> checkConstrTerms withExt p env ts =
>   case linear bvs of
>     Linear -> (foldr (bindVar . PIdent p) env bvs,ts)
>     NonLinear v -> errorAt p (duplicateVariable v)
>   where bvs = bv ts

> checkConstrTerm :: Bool -> Int -> Position -> ModuleIdent -> RenameEnv
>	             -> ConstrTerm -> RenameState ConstrTerm
> checkConstrTerm _ _ _ _ _ (LiteralPattern l) =
>   liftM LiteralPattern (renameLiteral l)
> checkConstrTerm _ _ _ _ _ (NegativePattern op l) =
>   liftM (NegativePattern op) (renameLiteral l)
> checkConstrTerm withExt k p m env (VariablePattern v)
>   | v == anonId 
>     = liftM (VariablePattern . renameIdent anonId) newId
>   | otherwise 
>     = checkConstrTerm withExt k p m env (ConstructorPattern (qualify v) [])
> checkConstrTerm withExt k p m env (ConstructorPattern c ts) -- =
>  | name (unqualify c) == "..." 
>    = error (show p ++ ": " ++ show c ++ "\n" ++ show (qualLookupVar c env))
>  | otherwise =
>   case qualLookupVar c env of
>     [Constr n]
>       | n == n' ->
>           liftM (ConstructorPattern c) 
>	          (mapM (checkConstrTerm withExt k p m env) ts)
>       | otherwise -> errorAt p (wrongArity c n n')
>       where n' = length ts
>     [r]
>       | null ts && not (isQualified c) ->
>	    return (VariablePattern (renameIdent (varIdent r) k))
>       | withExt ->
>           if n' >= n
>              then do ts' <- mapM (checkConstrTerm withExt k p m env) ts
>	               return (FunctionPattern (qualVarIdent r) ts')
>	       else errorAt p (partialFuncPatt c n n')
>       | otherwise -> errorAt p noFuncPattern  
>	where n = arity r
>	      n' = length ts
>     rs -> case (qualLookupVar (qualQualify m c) env) of
>             []
>               | null ts && not (isQualified c) ->
>	            return (VariablePattern (renameIdent (unqualify c) k))
>		| otherwise -> errorAt p (undefinedData c)
>             [Constr n]
>               | n == n' ->
>                   liftM (ConstructorPattern (qualQualify m c)) 
>                         (mapM (checkConstrTerm withExt k p m env) ts)
>               | otherwise -> errorAt p (wrongArity c n n')
>               where n' = length ts
>	      [r]
>	        | null ts && not (isQualified c) ->
>                   return (VariablePattern (renameIdent (varIdent r) k))
>               | withExt ->
>                   if n' >= n
>	               then do ts' <- mapM (checkConstrTerm withExt k p m env) ts
>			       return (FunctionPattern (qualVarIdent r) ts')
>		       else errorAt p (partialFuncPatt c n n')
>	        | otherwise -> errorAt p noFuncPattern
>               where n = arity r
>		      n' = length ts
>             _ -> errorAt p (ambiguousData c)
> checkConstrTerm withExt k p m env (InfixPattern t1 op t2) =
>   case (qualLookupVar op env) of
>     [Constr n]
>       | n == 2 ->
>           do t1' <- checkConstrTerm withExt k p m env t1
>	       t2' <- checkConstrTerm withExt k p m env t2
>              return (InfixPattern t1' op t2') 
>       | otherwise -> errorAt p (wrongArity op n 2)
>     [r]
>       | withExt ->
>           do t1' <- checkConstrTerm withExt k p m env t1
>	       t2' <- checkConstrTerm withExt k p m env t2
>              return (InfixFuncPattern t1' op t2')
>       | otherwise -> errorAt p noFuncPattern    
>     rs -> case (qualLookupVar (qualQualify m op) env) of
>             [] -> errorAt p (undefinedData op)
>             [Constr n]
>               | n == 2 ->
>                   do t1' <- checkConstrTerm withExt k p m env t1
>	               t2' <- checkConstrTerm withExt k p m env t2
>                      return (InfixPattern t1' (qualQualify m op) t2') 
>               | otherwise -> errorAt p (wrongArity op n 2)
>	      [r]
>               | withExt ->
>	            do t1' <- checkConstrTerm withExt k p m env t1
>	               t2' <- checkConstrTerm withExt k p m env t2
>		       return (InfixFuncPattern t1' (qualQualify m op) t2')
>	        | otherwise -> errorAt p noFuncPattern
>             _ -> errorAt p (ambiguousData op)
> checkConstrTerm withExt k p m env (ParenPattern t) =
>   liftM ParenPattern (checkConstrTerm withExt k p m env t)
> checkConstrTerm withExt k p m env (TuplePattern ts) =
>   liftM TuplePattern (mapM (checkConstrTerm withExt k p m env) ts)
> checkConstrTerm withExt k p m env (ListPattern ts) =
>   liftM ListPattern (mapM (checkConstrTerm withExt k p m env) ts)
> checkConstrTerm withExt k p m env (AsPattern v t) =
>   liftM (AsPattern (checkVar "@ pattern" k p env v))
>         (checkConstrTerm withExt k p m env t)
> checkConstrTerm withExt k p m env (LazyPattern t) =
>   liftM LazyPattern (checkConstrTerm withExt k p m env t)

> checkRhs :: Bool -> ModuleIdent -> RenameEnv -> Rhs -> RenameState Rhs
> checkRhs withExt m env (SimpleRhs p e ds) =
>   do
>     (env',ds') <- checkLocalDecls withExt m env ds
>     e' <- checkExpr withExt p m env' e
>     return (SimpleRhs p e' ds')
> checkRhs withExt m env (GuardedRhs es ds) =
>   do
>     (env',ds') <- checkLocalDecls withExt m env ds
>     es' <- mapM (checkCondExpr withExt m env') es
>     return (GuardedRhs es' ds')

> checkCondExpr :: Bool -> ModuleIdent -> RenameEnv -> CondExpr -> RenameState CondExpr
> checkCondExpr withExt m env (CondExpr p g e) =
>   do
>     g' <- checkExpr withExt p m env g
>     e' <- checkExpr withExt p m env e
>     return (CondExpr p g' e')

> checkExpr :: Bool -> Position -> ModuleIdent -> RenameEnv -> Expression 
>           -> RenameState Expression
> checkExpr _ _ _ _ (Literal l) = liftM Literal (renameLiteral l)
> checkExpr withExt p m env (Variable v) =
>   case (qualLookupVar v env) of
>     [] ->  errorAt p (undefinedVariable v)
>     [Constr _] -> return (Constructor v)
>     [GlobalVar _ _] -> return (Variable v)
>     [LocalVar _ v'] -> return (Variable (qualify v'))
>     rs -> case (qualLookupVar (qualQualify m v) env) of
>             [] -> errorAt p (ambiguousIdent rs v)
>             [Constr _] -> return (Constructor v)
>             [GlobalVar _ _] -> return (Variable v)
>             [LocalVar _ v'] -> return (Variable (qualify v'))
>             rs' -> errorAt p (ambiguousIdent rs' v)
> checkExpr withExt p m env (Constructor c) = 
>   checkExpr withExt p m env (Variable c)
> checkExpr withExt p m env (Paren e) = 
>   liftM Paren (checkExpr withExt p m env e)
> checkExpr withExt p m env (Typed e ty) = 
>   liftM (flip Typed ty) (checkExpr withExt p m env e)
> checkExpr withExt p m env (Tuple es) = 
>   liftM Tuple (mapM (checkExpr withExt p m env) es)
> checkExpr withExt p m env (List es) = 
>   liftM List (mapM (checkExpr withExt p m env) es)
> checkExpr withExt p m env (ListCompr e qs) =
>   do
>     (env',qs') <- mapAccumM (checkStatement withExt p m) env qs
>     e' <- checkExpr withExt p m env' e
>     return (ListCompr e' qs')
> checkExpr withExt p m env (EnumFrom e) = 
>   liftM EnumFrom (checkExpr withExt p m env e)
> checkExpr withExt p m env (EnumFromThen e1 e2) =
>   do
>     e1' <- checkExpr withExt p m env e1
>     e2' <- checkExpr withExt p m env e2
>     return (EnumFromThen e1' e2')
> checkExpr withExt p m env (EnumFromTo e1 e2) =
>   do
>     e1' <- checkExpr withExt p m env e1
>     e2' <- checkExpr withExt p m env e2
>     return (EnumFromTo e1' e2')
> checkExpr withExt p m env (EnumFromThenTo e1 e2 e3) =
>   do
>     e1' <- checkExpr withExt p m env e1
>     e2' <- checkExpr withExt p m env e2
>     e3' <- checkExpr withExt p m env e3
>     return (EnumFromThenTo e1' e2' e3')
> checkExpr withExt p m env (UnaryMinus op e) = 
>   liftM (UnaryMinus op) (checkExpr withExt p m env e)
> checkExpr withExt p m env (Apply e1 e2) =
>   do
>     e1' <- checkExpr withExt p m env e1
>     e2' <- checkExpr withExt p m env e2
>     return (Apply e1' e2')
> checkExpr withExt p m env (InfixApply e1 op e2) =
>   do
>     e1' <- checkExpr withExt p m env e1
>     e2' <- checkExpr withExt p m env e2
>     return (InfixApply e1' (checkOp p m env op) e2')
> checkExpr withExt p m env (LeftSection e op) =
>   liftM (flip LeftSection (checkOp p m env op)) (checkExpr withExt p m env e)
> checkExpr withExt p m env (RightSection op e) =
>   liftM (RightSection (checkOp p m env op)) (checkExpr withExt p m env e)
> checkExpr withExt p m env (Lambda ts e) =
>   do
>     (env',ts') <- checkArgs withExt p m env ts
>     e' <- checkExpr withExt p m env' e
>     return (Lambda ts' e')
> checkExpr withExt p m env (Let ds e) =
>   do
>     (env',ds') <- checkLocalDecls withExt m env ds
>     e' <- checkExpr withExt p m env' e
>     return (Let ds' e')
> checkExpr withExt p m env (Do sts e) =
>   do
>     (env',sts') <- mapAccumM (checkStatement withExt p m) env sts
>     e' <- checkExpr withExt p m env' e
>     return (Do sts' e')
> checkExpr withExt p m env (IfThenElse e1 e2 e3) =
>   do
>     e1' <- checkExpr withExt p m env e1
>     e2' <- checkExpr withExt p m env e2
>     e3' <- checkExpr withExt p m env e3
>     return (IfThenElse e1' e2' e3')
> checkExpr withExt p m env (Case e alts) =
>   do
>     e' <- checkExpr withExt p m env e
>     alts' <- mapM (checkAlt withExt m env) alts
>     return (Case e' alts')

> checkStatement :: Bool -> Position -> ModuleIdent -> RenameEnv -> Statement
>                -> RenameState (RenameEnv,Statement)
> checkStatement withExt p m env (StmtExpr e) =
>   do
>     e' <- checkExpr withExt p m env e
>     return (env,StmtExpr e')
> checkStatement withExt p m env (StmtBind t e) =
>   do
>     e' <- checkExpr withExt p m env e
>     (env',[t']) <- checkArgs withExt p m env [t]
>     return (env',StmtBind t' e')
> checkStatement withExt p m env (StmtDecl ds) =
>   do
>     (env',ds') <- checkLocalDecls withExt m env ds
>     return (env',StmtDecl ds')

> checkAlt :: Bool -> ModuleIdent -> RenameEnv -> Alt -> RenameState Alt
> checkAlt withExt m env (Alt p t rhs) =
>   do
>     (env',[t']) <- checkArgs withExt p m env [t]
>     rhs' <- checkRhs withExt m env' rhs
>     return (Alt p t' rhs')

> checkOp :: Position -> ModuleIdent -> RenameEnv -> InfixOp -> InfixOp
> checkOp p m env op =
>   case (qualLookupVar v env) of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> InfixConstr v
>     [GlobalVar _ _] -> InfixOp v
>     [LocalVar _ v'] -> InfixOp (qualify v')
>     rs -> case (qualLookupVar (qualQualify m v) env) of
>             [] -> errorAt p (ambiguousIdent rs v)
>             [Constr _] -> InfixConstr v
>             [GlobalVar _ _] -> InfixOp v
>             [LocalVar _ v'] -> InfixOp (qualify v')
>             rs' -> errorAt p (ambiguousIdent rs' v)
>   where v = opName op

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrs :: Decl -> [PIdent]
> constrs (DataDecl _ _ _ cs) = map constr cs
>   where constr (ConstrDecl p _ c _) = PIdent p c
>         constr (ConOpDecl p _ _ op _) = PIdent p op
> constrs (NewtypeDecl _ _ _ (NewConstrDecl p _ c _)) = [PIdent p c]
> constrs _ = []

> vars :: Decl -> [PIdent]
> vars (TypeSig p fs _) = map (PIdent p) fs
> vars (EvalAnnot p fs _) = map (PIdent p) fs
> vars (FunctionDecl p f _) = [PIdent p f]
> vars (ExternalDecl p _ _ f _) = [PIdent p f]
> vars (FlatExternalDecl p fs) = map (PIdent p) fs
> vars (PatternDecl p t _) = map (PIdent p) (bv t)
> vars (ExtraVariables p vs) = map (PIdent p) vs
> vars _ = []

> renameLiteral :: Literal -> RenameState Literal
> renameLiteral (Int v i) = liftM (flip Int i . renameIdent v) newId
> renameLiteral l = return l


Since the compiler expects all rules of the same function to be together,
it is necessary to sort the list of declarations.

> sortFuncDecls :: [Decl] -> [Decl]
> sortFuncDecls decls = sortFD emptyEnv [] decls
>  where
>  sortFD env res [] = reverse res
>  sortFD env res (decl:decls)
>     = case decl of
>	  FunctionDecl _ ident _
>	     | isJust (lookupEnv ident env)
>	       -> sortFD env (insertBy cmpFuncDecl decl res) decls
>	     | otherwise
>              -> sortFD (bindEnv ident () env) (decl:res) decls
>	  _    -> sortFD env (decl:res) decls

> cmpFuncDecl :: Decl -> Decl -> Ordering
> cmpFuncDecl (FunctionDecl _ id1 _) (FunctionDecl _ id2 _)
>    | id1 == id2 = EQ
>    | otherwise  = GT
> cmpFuncDecl decl1 decl2 = GT

> cmpPos :: Position -> Position -> Ordering
> cmpPos p1 p2 | lp1 < lp2  = LT
>              | lp1 == lp2 = EQ
>              | otherwise  = GT
>  where lp1 = line p1
>        lp2 = line p2

> getDeclPos :: Decl -> Position
> getDeclPos (ImportDecl pos _ _ _ _) = pos
> getDeclPos (InfixDecl pos _ _ _) = pos
> getDeclPos (DataDecl pos _ _ _) = pos
> getDeclPos (NewtypeDecl pos _ _ _) = pos
> getDeclPos (TypeDecl pos _ _ _) = pos
> getDeclPos (TypeSig pos _ _) = pos
> getDeclPos (EvalAnnot pos _ _) = pos
> getDeclPos (FunctionDecl pos _ _) = pos
> getDeclPos (ExternalDecl pos _ _ _ _) = pos
> getDeclPos (FlatExternalDecl pos _) = pos
> getDeclPos (PatternDecl pos _ _) = pos
> getDeclPos (ExtraVariables pos _) = pos

\end{verbatim}
Due to the lack of a capitalization convention in Curry, it is
possible that an identifier may ambiguously refer to a data
constructor and a function provided that both are imported from some
other module. When checking whether an identifier denotes a
constructor there are two options with regard to ambiguous
identifiers:
\begin{enumerate}
\item Handle the identifier as a data constructor if at least one of
  the imported names is a data constructor.
\item Handle the identifier as a data constructor only if all imported
  entities are data constructors.
\end{enumerate}
We choose the first possibility here because in the second case a
redefinition of a constructor can magically become possible if a
function with the same name is imported. It seems better to warn
the user about the fact that the identifier is ambiguous.
\begin{verbatim}

> isDataConstr :: Ident -> RenameEnv -> Bool
> isDataConstr v = any isConstr . lookupVar v . globalEnv . toplevelEnv

> isConstr :: RenameInfo -> Bool
> isConstr (Constr _) = True
> isConstr (GlobalVar _ _) = False
> isConstr (LocalVar _ _) = False

> varIdent :: RenameInfo -> Ident
> varIdent (GlobalVar _ v) = unqualify v
> varIdent (LocalVar _ v) =  v
> varIdent _ = internalError "not a variable"

> qualVarIdent :: RenameInfo -> QualIdent
> qualVarIdent (GlobalVar _ v) = v
> qualVarIdent (LocalVar _ v) = qualify v

> arity :: RenameInfo -> Int
> arity (Constr n) = n
> arity (GlobalVar n _) = n
> arity (LocalVar n _) = n


\end{verbatim}
Miscellaneous functions.
\begin{verbatim}

> typeArity :: TypeExpr -> Int
> typeArity (ArrowType _ t2) = 1 + typeArity t2
> typeArity _                = 0

> getFlatLhs :: Equation -> (Ident,[ConstrTerm])
> getFlatLhs (Equation  _ lhs _) = flatLhs lhs

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedVariable :: QualIdent -> String
> undefinedVariable v = qualName v ++ " is undefined"

> undefinedData :: QualIdent -> String
> undefinedData c = "Undefined data constructor " ++ qualName c

> ambiguousIdent :: [RenameInfo] -> QualIdent -> String
> ambiguousIdent rs
>   | any isConstr rs = ambiguousData
>   | otherwise = ambiguousVariable

> ambiguousVariable :: QualIdent -> String
> ambiguousVariable v = "Ambiguous variable " ++ qualName v

> ambiguousData :: QualIdent -> String
> ambiguousData c = "Ambiguous data constructor " ++ qualName c

> duplicateDefinition :: Ident -> String
> duplicateDefinition v = "More than one definition for " ++ name v

> duplicateVariable :: Ident -> String
> duplicateVariable v = name v ++ " occurs more than once in pattern"

> duplicateData :: Ident -> String
> duplicateData c = "More than one definition for data constructor " ++ name c

> duplicateTypeSig :: Ident -> String
> duplicateTypeSig v = "More than one type signature for " ++ name v

> duplicateEvalAnnot :: Ident -> String
> duplicateEvalAnnot v = "More than one eval annotation for " ++ name v

> nonVariable :: String -> Ident -> String
> nonVariable what c =
>   "Data constructor " ++ name c ++ " in left hand side of " ++ what

> noFuncPattern :: String
> noFuncPattern = "function pattern not supported"

> noBody :: Ident -> String
> noBody v = "No body for " ++ name v

> noTypeSig :: Ident -> String
> noTypeSig f = "No type signature for external function " ++ name f

> noToplevelPattern :: String
> noToplevelPattern = "Pattern declaration not allowed at top-level"

> differentArity :: Ident -> String
> differentArity f = "Equations for " ++ name f ++ " have different arities"

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity c arity argc =
>   "Data constructor " ++ qualName c ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> partialFuncPatt :: QualIdent -> Int -> Int -> String
> partialFuncPatt f arity argc =
>    "Function pattern " ++ qualName f ++ " expects at least " 
>    ++ arguments arity ++ " but is applied to " ++ show argc
>  where arguments 0 = "no arguments"
>        arguments 1 = "1 argument"
>        arguments n = show n ++ " arguments"

> noExpressionStatement :: String
> noExpressionStatement =
>   "Last statement in a do expression must be an expression"

\end{verbatim}
