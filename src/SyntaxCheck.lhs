% -*- LaTeX -*-
% $Id: SyntaxCheck.lhs,v 1.53 2004/02/15 22:10:37 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
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

> module SyntaxCheck(syntaxCheck,syntaxCheckGoal) where
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

> syntaxCheck :: ModuleIdent -> ValueEnv -> [Decl] -> [Decl]
> syntaxCheck m tyEnv ds =
>   case linear (concatMap constrs tds) of
>     Linear -> tds ++ run (checkModule m env vds)
>     NonLinear (PIdent p c) -> errorAt p (duplicateData c)
>   where (tds,vds) = partition isTypeDecl ds
>         env = foldr (bindConstrs m) (globalEnv (fmap renameInfo tyEnv)) tds

> syntaxCheckGoal :: ValueEnv -> Goal -> Goal
> syntaxCheckGoal tyEnv g =
>   run (checkGoal (globalEnv (fmap renameInfo tyEnv)) g)

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
environment records the new name of the variable after renaming. No
further information is needed for global variables.
\begin{verbatim}

> type RenameEnv = NestEnv RenameInfo
> data RenameInfo = Constr Int | GlobalVar | LocalVar Ident deriving (Eq,Show)

> globalKey :: Int
> globalKey = uniqueId (mkIdent "")

> renameInfo :: ValueInfo -> RenameInfo
> renameInfo (DataConstructor _ (ForAllExist _ _ ty)) = Constr (arrowArity ty)
> renameInfo (NewtypeConstructor _ _) = Constr 1
> renameInfo _ = GlobalVar

> bindConstrs :: ModuleIdent -> Decl -> RenameEnv -> RenameEnv
> bindConstrs m (DataDecl _ tc _ cs) env = foldr (bindConstr m) env cs
> bindConstrs m (NewtypeDecl _ tc _ nc) env = bindNewConstr m nc env
> bindConstrs _ _ env = env

> bindConstr :: ModuleIdent -> ConstrDecl -> RenameEnv -> RenameEnv
> bindConstr m (ConstrDecl _ _ c tys) = bindGlobal m c (Constr (length tys))
> bindConstr m (ConOpDecl _ _ _ op _) = bindGlobal m op (Constr 2)

> bindNewConstr :: ModuleIdent -> NewConstrDecl -> RenameEnv -> RenameEnv
> bindNewConstr m (NewConstrDecl _ _ c _) = bindGlobal m c (Constr 1)

> bindFunc :: ModuleIdent -> PIdent -> RenameEnv -> RenameEnv
> bindFunc m (PIdent p f) = bindGlobal m f GlobalVar

> bindVar :: PIdent -> RenameEnv -> RenameEnv
> bindVar (PIdent p v) env
>   | v' == anonId = env
>   | otherwise = bindLocal v' (LocalVar v) env
>   where v' = unRenameIdent v

> bindGlobal :: ModuleIdent -> Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindGlobal m c r = bindNestEnv c r . qualBindNestEnv (qualifyWith m c) r

> bindLocal :: Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindLocal f r = bindNestEnv f r

> lookupVar :: Ident -> RenameEnv -> [RenameInfo]
> lookupVar v env = lookupNestEnv v env ++! lookupTupleConstr v

> qualLookupVar :: QualIdent -> RenameEnv -> [RenameInfo]
> qualLookupVar v env =
>   qualLookupNestEnv v env ++! lookupTupleConstr (unqualify v)

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

> checkModule :: ModuleIdent -> RenameEnv -> [Decl] -> RenameState [Decl]
> checkModule m env ds = liftM snd (checkTopDecls m env ds)

> checkTopDecls :: ModuleIdent -> RenameEnv -> [Decl]
>               -> RenameState (RenameEnv,[Decl])
> checkTopDecls m env ds = checkDeclGroup (bindFunc m) globalKey env ds

> checkGoal :: RenameEnv -> Goal -> RenameState Goal
> checkGoal env (Goal p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Goal p e' ds')

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

> checkLocalDecls :: RenameEnv -> [Decl] -> RenameState (RenameEnv,[Decl])
> checkLocalDecls env ds =
>   newId >>= \k -> checkDeclGroup bindVar k (nestEnv env) ds

> checkDeclGroup :: (PIdent -> RenameEnv -> RenameEnv) -> Int -> RenameEnv
>                -> [Decl] -> RenameState (RenameEnv,[Decl])
> checkDeclGroup bindVar k env ds =
>   mapM (checkDeclLhs k env) ds >>=
>   checkDecls bindVar env . joinEquations

> checkDeclLhs :: Int -> RenameEnv -> Decl -> RenameState Decl
> checkDeclLhs k _ (InfixDecl p fix pr ops) =
>   return (InfixDecl p fix pr (map (flip renameIdent k) ops))
> checkDeclLhs k env (TypeSig p vs ty) =
>   return (TypeSig p (map (checkVar "type signature" k p env) vs) ty)
> checkDeclLhs k env (EvalAnnot p fs ev) =
>   return (EvalAnnot p (map (checkVar "evaluation annotation" k p env) fs) ev)
> checkDeclLhs k env (FunctionDecl p _ eqs) = checkEquationLhs k env p eqs
> checkDeclLhs k env (ExternalDecl p cc ie f ty) =
>   return (ExternalDecl p cc ie (checkVar "external declaration" k p env f) ty)
> checkDeclLhs k env (FlatExternalDecl p fs) =
>   return (FlatExternalDecl p
>             (map (checkVar "external declaration" k p env) fs))
> checkDeclLhs k env (PatternDecl p t rhs) =
>   do
>     t' <- checkConstrTerm k p env t
>     return (PatternDecl p t' rhs)
> checkDeclLhs k env (ExtraVariables p vs) =
>   return (ExtraVariables p
>             (map (checkVar "free variables declaration" k p env) vs))
> checkDeclLhs _ _ d = return d

> checkEquationLhs :: Int -> RenameEnv -> Position -> [Equation]
>                  -> RenameState Decl
> checkEquationLhs k env p [Equation p' lhs rhs] =
>   either (return . funDecl) (checkDeclLhs k env . patDecl)
>          (checkEqLhs k env p' lhs)
>   where funDecl (f,lhs) = FunctionDecl p f [Equation p' lhs rhs]
>         patDecl t
>           | k == globalKey = errorAt p noToplevelPattern
>           | otherwise = PatternDecl p' t rhs
> checkEquationLhs _ _ _ _ = internalError "checkEquationLhs"

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

> checkDecls :: (PIdent -> RenameEnv -> RenameEnv) -> RenameEnv -> [Decl]
>            -> RenameState (RenameEnv,[Decl])
> checkDecls bindVar env ds =
>   case linear bvs of
>     Linear ->
>       case linear tys of
>         Linear ->
>           case linear evs of
>             Linear ->
>               case filter (`notElem` tys) fs' of
>                 [] -> liftM ((,) env') (mapM (checkDeclRhs bvs env') ds)
>                 PIdent p f : _ -> errorAt p (noTypeSig f)
>             NonLinear (PIdent p v) -> errorAt p (duplicateEvalAnnot v)
>         NonLinear (PIdent p v) -> errorAt p (duplicateTypeSig v)
>     NonLinear (PIdent p v) -> errorAt p (duplicateDefinition v)
>   where bvs = concat (map vars (filter isValueDecl ds))
>         tys = concat (map vars (filter isTypeSig ds))
>         evs = concat (map vars (filter isEvalAnnot ds))
>         fs' = [PIdent p f | FlatExternalDecl p fs <- ds, f <- fs]
>         env' = foldr bindVar env bvs

> checkDeclRhs :: [PIdent] -> RenameEnv -> Decl -> RenameState Decl
> checkDeclRhs bvs _ (TypeSig p vs ty) =
>   return (TypeSig p (map (checkLocalVar bvs p) vs) ty)
> checkDeclRhs bvs _ (EvalAnnot p vs ev) =
>   return (EvalAnnot p (map (checkLocalVar bvs p) vs) ev)
> checkDeclRhs _ env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (checkEquation env) eqs)
> checkDeclRhs _ env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (checkRhs env rhs)
> checkDeclRhs _ _ d = return d

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

> checkEquation :: RenameEnv -> Equation -> RenameState Equation
> checkEquation env (Equation p lhs rhs) =
>   do
>     (env',lhs') <- checkLhs p env lhs
>     rhs' <- checkRhs env' rhs
>     return (Equation p lhs' rhs')

> checkLhs :: Position -> RenameEnv -> Lhs -> RenameState (RenameEnv,Lhs)
> checkLhs p env lhs =
>   newId >>= \k ->
>   checkLhsTerm k p env lhs >>=
>   return . checkConstrTerms p (nestEnv env)

> checkLhsTerm :: Int -> Position -> RenameEnv -> Lhs -> RenameState Lhs
> checkLhsTerm k p env (FunLhs f ts) =
>   do
>     ts' <- mapM (checkConstrTerm k p env) ts
>     return (FunLhs f ts')
> checkLhsTerm k p env (OpLhs t1 op t2) =
>   do
>     t1' <- checkConstrTerm k p env t1
>     t2' <- checkConstrTerm k p env t2
>     return (OpLhs t1' op t2')
> checkLhsTerm k p env (ApLhs lhs ts) =
>   do
>     lhs' <- checkLhsTerm k p env lhs
>     ts' <- mapM (checkConstrTerm k p env) ts
>     return (ApLhs lhs' ts')

> checkArgs :: Position -> RenameEnv -> [ConstrTerm]
>           -> RenameState (RenameEnv,[ConstrTerm])
> checkArgs p env ts =
>   newId >>= \k ->
>   mapM (checkConstrTerm k p env) ts >>=
>   return . checkConstrTerms p (nestEnv env)

> checkConstrTerms :: QuantExpr t => Position -> RenameEnv -> t
>                  -> (RenameEnv,t)
> checkConstrTerms p env ts =
>   case linear bvs of
>     Linear -> (foldr (bindVar . PIdent p) env bvs,ts)
>     NonLinear v -> errorAt p (duplicateVariable v)
>   where bvs = bv ts

> checkConstrTerm :: Int -> Position -> RenameEnv -> ConstrTerm
>                 -> RenameState ConstrTerm
> checkConstrTerm _ _ _ (LiteralPattern l) =
>   liftM LiteralPattern (renameLiteral l)
> checkConstrTerm _ _ _ (NegativePattern op l) =
>   liftM (NegativePattern op) (renameLiteral l)
> checkConstrTerm k p env (VariablePattern v)
>   | v == anonId = liftM (VariablePattern . renameIdent anonId) newId
>   | otherwise = checkConstrTerm k p env (ConstructorPattern (qualify v) [])
> checkConstrTerm k p env (ConstructorPattern c ts) =
>   case qualLookupVar c env of
>     [Constr n]
>       | n == n' ->
>           liftM (ConstructorPattern c) (mapM (checkConstrTerm k p env) ts)
>       | otherwise -> errorAt p (wrongArity c n n')
>       where n' = length ts
>     rs
>       | any isConstr rs -> errorAt p (ambiguousData c)
>       | not (isQualified c) && null ts ->
>           return (VariablePattern (renameIdent (unqualify c) k))
>       | otherwise -> errorAt p (undefinedData c)
> checkConstrTerm k p env (InfixPattern t1 op t2) =
>   case qualLookupVar op env of
>     [Constr n]
>       | n == 2 ->
>           do
>             t1' <- checkConstrTerm k p env t1
>             t2' <- checkConstrTerm k p env t2
>             return (InfixPattern t1' op t2')
>       | otherwise -> errorAt p (wrongArity op n 2)
>     rs
>       | any isConstr rs -> errorAt p (ambiguousData op)
>       | otherwise -> errorAt p (undefinedData op)
> checkConstrTerm k p env (ParenPattern t) =
>   liftM ParenPattern (checkConstrTerm k p env t)
> checkConstrTerm k p env (TuplePattern ts) =
>   liftM TuplePattern (mapM (checkConstrTerm k p env) ts)
> checkConstrTerm k p env (ListPattern ts) =
>   liftM ListPattern (mapM (checkConstrTerm k p env) ts)
> checkConstrTerm k p env (AsPattern v t) =
>   liftM (AsPattern (checkVar "@ pattern" k p env v))
>         (checkConstrTerm k p env t)
> checkConstrTerm k p env (LazyPattern t) =
>   liftM LazyPattern (checkConstrTerm k p env t)

> checkRhs :: RenameEnv -> Rhs -> RenameState Rhs
> checkRhs env (SimpleRhs p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (SimpleRhs p e' ds')
> checkRhs env (GuardedRhs es ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     es' <- mapM (checkCondExpr env') es
>     return (GuardedRhs es' ds')

> checkCondExpr :: RenameEnv -> CondExpr -> RenameState CondExpr
> checkCondExpr env (CondExpr p g e) =
>   do
>     g' <- checkExpr p env g
>     e' <- checkExpr p env e
>     return (CondExpr p g' e')

> checkExpr :: Position -> RenameEnv -> Expression -> RenameState Expression
> checkExpr _ _ (Literal l) = liftM Literal (renameLiteral l)
> checkExpr p env (Variable v) =
>   case qualLookupVar v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> return (Constructor v)
>     [GlobalVar] -> return (Variable v)
>     [LocalVar v'] -> return (Variable (qualify v'))
>     rs -> errorAt p (ambiguousIdent rs v)
> checkExpr p env (Constructor c) = checkExpr p env (Variable c)
> checkExpr p env (Paren e) = liftM Paren (checkExpr p env e)
> checkExpr p env (Typed e ty) = liftM (flip Typed ty) (checkExpr p env e)
> checkExpr p env (Tuple es) = liftM Tuple (mapM (checkExpr p env) es)
> checkExpr p env (List es) = liftM List (mapM (checkExpr p env) es)
> checkExpr p env (ListCompr e qs) =
>   do
>     (env',qs') <- mapAccumM (checkStatement p) env qs
>     e' <- checkExpr p env' e
>     return (ListCompr e' qs')
> checkExpr p env (EnumFrom e) = liftM EnumFrom (checkExpr p env e)
> checkExpr p env (EnumFromThen e1 e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (EnumFromThen e1' e2')
> checkExpr p env (EnumFromTo e1 e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (EnumFromTo e1' e2')
> checkExpr p env (EnumFromThenTo e1 e2 e3) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     e3' <- checkExpr p env e3
>     return (EnumFromThenTo e1' e2' e3')
> checkExpr p env (UnaryMinus op e) = liftM (UnaryMinus op) (checkExpr p env e)
> checkExpr p env (Apply e1 e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (Apply e1' e2')
> checkExpr p env (InfixApply e1 op e2) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     return (InfixApply e1' (checkOp p env op) e2')
> checkExpr p env (LeftSection e op) =
>   liftM (flip LeftSection (checkOp p env op)) (checkExpr p env e)
> checkExpr p env (RightSection op e) =
>   liftM (RightSection (checkOp p env op)) (checkExpr p env e)
> checkExpr p env (Lambda ts e) =
>   do
>     (env',ts') <- checkArgs p env ts
>     e' <- checkExpr p env' e
>     return (Lambda ts' e')
> checkExpr p env (Let ds e) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Let ds' e')
> checkExpr p env (Do sts e) =
>   do
>     (env',sts') <- mapAccumM (checkStatement p) env sts
>     e' <- checkExpr p env' e
>     return (Do sts' e')
> checkExpr p env (IfThenElse e1 e2 e3) =
>   do
>     e1' <- checkExpr p env e1
>     e2' <- checkExpr p env e2
>     e3' <- checkExpr p env e3
>     return (IfThenElse e1' e2' e3')
> checkExpr p env (Case e alts) =
>   do
>     e' <- checkExpr p env e
>     alts' <- mapM (checkAlt env) alts
>     return (Case e' alts')

> checkStatement :: Position -> RenameEnv -> Statement
>                -> RenameState (RenameEnv,Statement)
> checkStatement p env (StmtExpr e) =
>   do
>     e' <- checkExpr p env e
>     return (env,StmtExpr e')
> checkStatement p env (StmtBind t e) =
>   do
>     e' <- checkExpr p env e
>     (env',[t']) <- checkArgs p env [t]
>     return (env',StmtBind t' e')
> checkStatement p env (StmtDecl ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     return (env',StmtDecl ds')

> checkAlt :: RenameEnv -> Alt -> RenameState Alt
> checkAlt env (Alt p t rhs) =
>   do
>     (env',[t']) <- checkArgs p env [t]
>     rhs' <- checkRhs env' rhs
>     return (Alt p t' rhs')

> checkOp :: Position -> RenameEnv -> InfixOp -> InfixOp
> checkOp p env op =
>   case qualLookupVar v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> InfixConstr v
>     [GlobalVar] -> InfixOp v
>     [LocalVar v'] -> InfixOp (qualify v')
>     rs -> errorAt p (ambiguousIdent rs v)
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
> isConstr GlobalVar = False
> isConstr (LocalVar _) = False

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

> noExpressionStatement :: String
> noExpressionStatement =
>   "Last statement in a do expression must be an expression"

\end{verbatim}
