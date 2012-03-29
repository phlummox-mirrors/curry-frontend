% $Id: SyntaxCheck.lhs,v 1.53 2004/02/15 22:10:37 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% Modified by Björn Peemöller (bjp@informatik.uni-kiel.de)
%
\nwfilename{SyntaxCheck.lhs}
\section{Syntax Checks}
After the type declarations have been checked, the compiler performs a syntax
check on the remaining declarations. This check disambiguates nullary data
constructors and variables which -- in contrast to Haskell -- is not possible
on purely syntactic criteria. In addition, this pass checks for undefined as
well as ambiguous variables and constructors. In order to allow lifting of
local definitions in later phases, all local variables are renamed by adding a
key identifying their scope. Therefore, all variables defined in the same
scope share the same key so that multiple definitions can be recognized.
Finally, all (adjacent) equations of a function are merged into a single
definition.
\begin{verbatim}

> module Checks.SyntaxCheck (syntaxCheck) where

> import Control.Monad (liftM, liftM2, liftM3, unless, when)
> import qualified Control.Monad.State as S (State, runState, gets, modify)
> import Data.List ((\\), insertBy, partition)
> import Data.Maybe (fromJust, isJust, isNothing, maybeToList)
> import qualified Data.Set as Set (empty, insert, member)

> import Curry.Base.Ident
> import Curry.Base.Position
> import Curry.Syntax

> import Base.Expr
> import Base.Messages (Message, toMessage, internalError, posErr, qposErr)
> import Base.NestEnv
> import Base.Types
> import Base.Utils ((++!), findDouble, findMultiples)

> import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
> import Env.Value (ValueEnv, ValueInfo (..))

> import CompilerOpts

\end{verbatim}
The syntax checking proceeds as follows. First, the compiler extracts
information about all imported values and data constructors from the
imported (type) environments. Next, the data constructors defined in
the current module are entered into this environment. After this,
all record labels are entered into the environment too. If a record
identifier is already assigned to a constructor, then an error will be
generated. Finally, all declarations are checked within the resulting
environment. In addition, this process will also rename the local variables.
\begin{verbatim}

> syntaxCheck :: Options -> ModuleIdent -> ValueEnv -> TCEnv -> [Decl]
>             -> ([Decl], [Message])
> syntaxCheck opts m tyEnv tcEnv decls =
>   case findMultiples $ concatMap constrs typeDecls of
>     []  -> runSC (checkModule decls) state
>     css -> (decls, map errMultipleDataConstructor css)
>   where
>     typeDecls  = filter isTypeDecl decls
>     rEnv       = globalEnv $ fmap (renameInfo tcEnv) tyEnv
>     state      = initState (optExtensions opts) m rEnv

\end{verbatim}
A global state transformer is used for generating fresh integer keys with
which the variables are renamed.
The state tracks the identifier of the current scope 'scopeId' as well as the
next fresh identifier, which is used for introducing new scopes as well as
renaming literals and underscore to disambiguate them.
\begin{verbatim}

> -- |Syntax check monad
> type SCM = S.State SCState

> -- |Internal state of the syntax check
> data SCState = SCState
>   { extensions  :: [Extension] -- ^ Enabled language extensions
>   , moduleIdent :: ModuleIdent -- ^ 'ModuleIdent' of the current module
>   , renameEnv   :: RenameEnv   -- ^ Information store
>   , scopeId     :: Integer     -- ^ Identifier for the current scope
>   , nextId      :: Integer     -- ^ Next fresh identifier
>   , errors      :: [Message]   -- ^ Syntactic errors in the module
>   }

> -- |Initial syntax check state
> initState :: [Extension] -> ModuleIdent -> RenameEnv -> SCState
> initState exts m rEnv = SCState exts m rEnv globalScopeId 1 []

> -- |Identifier for global (top-level) declarations
> globalScopeId :: Integer
> globalScopeId = uniqueId (mkIdent "")

> -- |Run the syntax check monad
> runSC :: SCM a -> SCState -> (a, [Message])
> runSC scm s = let (a, s') = S.runState scm s in (a, reverse $ errors s')

> -- |Check for an enabled extension
> hasExtension :: Extension -> SCM Bool
> hasExtension ext = S.gets (elem ext . extensions)

> -- |Enable an additional 'Extension' to avoid redundant complaints about
> -- missing extensions
> enableExtension :: Extension -> SCM ()
> enableExtension e = S.modify $ \ s -> s { extensions = e : extensions s }

> -- |Retrieve the 'ModuleIdent' of the current module
> getModuleIdent :: SCM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> -- |Retrieve the 'RenameEnv'
> getRenameEnv :: SCM RenameEnv
> getRenameEnv = S.gets renameEnv

> -- |Modify the 'RenameEnv'
> modifyRenameEnv :: (RenameEnv -> RenameEnv) -> SCM ()
> modifyRenameEnv f = S.modify $ \ s -> s { renameEnv = f $ renameEnv s }

> -- |Retrieve the current scope identifier
> getScopeId :: SCM Integer
> getScopeId = S.gets scopeId

> -- |Create a new identifier and return it
> newId :: SCM Integer
> newId = do
>   curId <- S.gets nextId
>   S.modify $ \ s -> s { nextId = succ curId }
>   return curId

> -- |Increase the nesting of the 'RenameEnv' to introduce a new local scope.
> -- This also increases the scope identifier.
> incNesting :: SCM ()
> incNesting = do
>   newScopeId <- newId
>   S.modify $ \ s -> s { scopeId = newScopeId }
>   modifyRenameEnv nestEnv

> withLocalEnv :: SCM a -> SCM a
> withLocalEnv act = do
>   oldEnv <- getRenameEnv
>   res    <- act
>   modifyRenameEnv $ const oldEnv
>   return res

> -- |Perform an action in a nested scope (by creating a nested 'RenameEnv')
> -- and discard the nested 'RenameEnv' afterwards
> inNestedScope :: SCM a -> SCM a
> inNestedScope act = withLocalEnv (incNesting >> act)

> -- |Report a syntax error
> report :: Message -> SCM ()
> report msg = S.modify $ \ s -> s { errors = msg : errors s }

\end{verbatim}
A nested environment is used for recording information about the data
constructors and variables in the module. For every data constructor
its arity is saved. This is used for checking that all constructor
applications in patterns are saturated. For local variables the
environment records the new name of the variable after renaming.
Global variables are recorded with qualified identifiers in order
to distinguish multiply declared entities.

Currently, records must explicitly be declared together with their labels.
When constructing or updating a record, it is necessary to compute
all its labels using just one of them. Thus for each label
the record identifier and all its labels are entered into the environment

\em{Note:} the function \texttt{qualLookupVar} has been extended to
allow the usage of the qualified list constructor \texttt{(prelude.:)}.
\begin{verbatim}

> type RenameEnv = NestEnv RenameInfo

> data RenameInfo
>   -- |Arity of data constructor
>   = Constr Int
>   -- |Record type and all labels for a single record label
>   | RecordLabel QualIdent [Ident]
>   -- |Arity of global function
>   | GlobalVar Int QualIdent
>   -- |Arity of local function
>   | LocalVar Int Ident
>     deriving (Eq, Show)

\end{verbatim}
Since record types are currently translated into data types, it is necessary
to ensure that all identifiers for records and constructors are different.
Furthermore, it is not allowed to declare a label more than once.
\begin{verbatim}

> renameInfo :: TCEnv -> ValueInfo -> RenameInfo
> renameInfo _     (DataConstructor  _ a _) = Constr $ a
> renameInfo _     (NewtypeConstructor _ _) = Constr 1
> renameInfo _     (Value          qid a _) = GlobalVar a qid
> renameInfo tcEnv (Label            _ r _) = case qualLookupTC r tcEnv of
>   [AliasType _ _ (TypeRecord fs _)] -> RecordLabel r $ map fst fs
>   _ -> internalError $ "SyntaxCheck.renameInfo: ambiguous record " ++ show r

> bindGlobal :: ModuleIdent -> Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindGlobal m c r = bindNestEnv c r . qualBindNestEnv (qualifyWith m c) r

> bindLocal :: Ident -> RenameInfo -> RenameEnv -> RenameEnv
> bindLocal = bindNestEnv

------------------------------------------------------------------------------

> -- |Bind type constructor information
> bindTypeDecl :: Decl -> SCM ()
> bindTypeDecl (DataDecl    _ _ _ cs) = mapM_ bindConstr cs
> bindTypeDecl (NewtypeDecl _ _ _ nc) = bindNewConstr nc
> bindTypeDecl (TypeDecl _ t _ (RecordType fs _)) = do
>   m <- getModuleIdent
>   others <- qualLookupVar (qualifyWith m t) `liftM` getRenameEnv
>   when (any isConstr others) $ report $ errIllegalRecordId t
>   mapM_ (bindRecordLabel t allLabels) allLabels
>   where allLabels = concatMap fst fs
> bindTypeDecl _ = return ()

> bindConstr :: ConstrDecl -> SCM ()
> bindConstr (ConstrDecl _ _ c tys) = do
>   m <- getModuleIdent
>   modifyRenameEnv $ bindGlobal m c (Constr $ length tys)
> bindConstr (ConOpDecl _ _ _ op _) = do
>   m <- getModuleIdent
>   modifyRenameEnv $ bindGlobal m op (Constr 2)

> bindNewConstr :: NewConstrDecl -> SCM ()
> bindNewConstr (NewConstrDecl _ _ c _) = do
>   m <- getModuleIdent
>   modifyRenameEnv $ bindGlobal m c (Constr 1)

> bindRecordLabel :: Ident -> [Ident] -> Ident -> SCM ()
> bindRecordLabel t allLabels l = do
>   m <- getModuleIdent
>   new <- (null . lookupVar l) `liftM` getRenameEnv
>   unless new $ report $ errDuplicateDefinition l
>   modifyRenameEnv $ bindGlobal m l (RecordLabel (qualifyWith m t) allLabels)

------------------------------------------------------------------------------

> -- |Bind a global function declaration in the 'RenameEnv'
> bindFuncDecl :: ModuleIdent -> Decl -> RenameEnv -> RenameEnv
> bindFuncDecl m (FunctionDecl _ ident equs) env
>   | null equs = internalError "SyntaxCheck.bindFuncDecl: no equations"
>   | otherwise = let arty = length $ snd $ getFlatLhs $ head equs
>                     qid  = qualifyWith m ident
>                 in  bindGlobal m ident (GlobalVar arty qid) env
> bindFuncDecl m (ExternalDecl _ _ _ ident texpr) env
>   = let arty = typeArity texpr
>         qid  = qualifyWith m ident
>     in bindGlobal m ident (GlobalVar arty qid) env
> bindFuncDecl m (TypeSig _ ids texpr) env
>   = foldr bindTS env $ map (qualifyWith m) ids
>  where
>  bindTS qid env'
>   | null $ qualLookupVar qid env'
>   = bindGlobal m (unqualify qid) (GlobalVar (typeArity texpr) qid) env'
>   | otherwise
>   = env'
> bindFuncDecl _ _ env = env

------------------------------------------------------------------------------

> -- |Bind a local declaration (function, variables) in the 'RenameEnv'
> bindVarDecl :: Decl -> RenameEnv -> RenameEnv
> bindVarDecl (FunctionDecl _ ident equs) env
>   | null equs = internalError "SyntaxCheck.bindVarDecl: no equations"
>   | otherwise = let arty = length $ snd $ getFlatLhs $ head equs
>                 in  bindLocal (unRenameIdent ident) (LocalVar arty ident) env
> bindVarDecl (PatternDecl         _ t _) env = foldr bindVar env (bv t)
> bindVarDecl (ExtraVariables       _ vs) env = foldr bindVar env vs
> bindVarDecl _                           env = env

> bindVar :: Ident -> RenameEnv -> RenameEnv
> bindVar v env
>   | v' == anonId = env
>   | otherwise    = bindLocal v' (LocalVar 0 v) env
>   where v' = unRenameIdent v

> lookupVar :: Ident -> RenameEnv -> [RenameInfo]
> lookupVar v env = lookupNestEnv v env ++! lookupTupleConstr v

> qualLookupVar :: QualIdent -> RenameEnv -> [RenameInfo]
> qualLookupVar v env =  qualLookupNestEnv v env
>                    ++! qualLookupListCons v env
>                    ++! lookupTupleConstr (unqualify v)

> lookupTupleConstr :: Ident -> [RenameInfo]
> lookupTupleConstr v
>   | isTupleId v = [Constr $ tupleArity v]
>   | otherwise   = []

> qualLookupListCons :: QualIdent -> RenameEnv -> [RenameInfo]
> qualLookupListCons v env
>   | v == qualifyWith preludeMIdent consId
>   = qualLookupNestEnv (qualify $ qualidId v) env
>   | otherwise
>   = []

\end{verbatim}
When a module is checked, the global declaration group is checked. The
resulting renaming environment can be discarded. The same is true for
a goal. Note that all declarations in the goal must be considered as
local declarations.
\begin{verbatim}

> checkModule :: [Decl] -> SCM [Decl]
> checkModule decls = do
>   mapM_ bindTypeDecl (rds ++ dds)
>   liftM2 (++) (mapM checkTypeDecl tds) (checkTopDecls vds)
>   where (tds, vds) = partition isTypeDecl decls
>         (rds, dds) = partition isRecordDecl tds

> checkTypeDecl :: Decl -> SCM Decl
> checkTypeDecl rec@(TypeDecl _ r _ (RecordType fs rty)) = do
>   checkRecordExtension $ positionOfIdent r
>   when (isJust  rty) $ internalError
>                        "SyntaxCheck.checkTypeDecl: illegal record type"
>   when (null     fs) $ report $ errEmptyRecord $ positionOfIdent r
>   return rec
> checkTypeDecl d = return d

> checkTopDecls :: [Decl] -> SCM [Decl]
> checkTopDecls decls = do
>   m <- getModuleIdent
>   checkDeclGroup (bindFuncDecl m) decls

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

> checkDeclGroup :: (Decl -> RenameEnv -> RenameEnv) -> [Decl] -> SCM [Decl]
> checkDeclGroup bindDecl ds = do
>   checkedLhs <- mapM checkDeclLhs $ sortFuncDecls ds
>   joinEquations checkedLhs >>= checkDecls bindDecl

> checkDeclLhs :: Decl -> SCM Decl
> checkDeclLhs (InfixDecl   p fix' pr ops) =
>   InfixDecl p fix' pr `liftM` mapM renameVar ops
> checkDeclLhs (TypeSig           p vs ty) =
>   (\vs' -> TypeSig p vs' ty) `liftM` mapM (checkVar "type signature") vs
> checkDeclLhs (EvalAnnot         p fs ev) =
>   (\fs' -> EvalAnnot p fs' ev) `liftM` mapM (checkVar "evaluation annotation") fs
> checkDeclLhs (FunctionDecl      p _ eqs) =
>   checkEquationsLhs p eqs
> checkDeclLhs (ExternalDecl p cc ie f ty) =
>   (\f' -> ExternalDecl p cc ie f' ty) `liftM` checkVar "external declaration" f
> checkDeclLhs (FlatExternalDecl     p fs) =
>   FlatExternalDecl p `liftM` mapM (checkVar "flat external declaration") fs
> checkDeclLhs (PatternDecl       p t rhs) =
>     (\t' -> PatternDecl p t' rhs) `liftM` checkConstrTerm p t
> checkDeclLhs (ExtraVariables       p vs) =
>   ExtraVariables p `liftM` mapM (checkVar "free variables declaration") vs
> checkDeclLhs d                           = return d

> checkVar :: String -> Ident -> SCM Ident
> checkVar _what v = do
>   -- isDC <- S.gets (isDataConstr v . renameEnv)
>   -- when isDC $ report $ nonVariable what v -- TODO Why is this disabled?
>   renameVar v

> renameVar :: Ident -> SCM Ident
> renameVar v = renameIdent v `liftM` getScopeId

> checkEquationsLhs :: Position -> [Equation] -> SCM Decl
> checkEquationsLhs p [Equation p' lhs rhs] = do
>   lhs' <- checkEqLhs p' lhs
>   case lhs' of
>     Left  l -> return $ funDecl l
>     Right r -> patDecl r >>= checkDeclLhs
>   where funDecl (f, lhs') = FunctionDecl p f [Equation p' lhs' rhs]
>         patDecl t = do
>           k <- getScopeId
>           when (k == globalScopeId) $ report $ errToplevelPattern p
>           return $ PatternDecl p' t rhs
> checkEquationsLhs _ _ = internalError "SyntaxCheck.checkEquationsLhs"

> checkEqLhs :: Position -> Lhs -> SCM (Either (Ident, Lhs) ConstrTerm)
> checkEqLhs p toplhs = do
>   m   <- getModuleIdent
>   k   <- getScopeId
>   env <- getRenameEnv
>   case toplhs of
>     FunLhs f ts
>       | not $ isDataConstr f env -> return left
>       | k /= globalScopeId       -> return right
>       | null infos               -> return left
>       | otherwise                -> do report $ errToplevelPattern p
>                                        return right
>       where f'    = renameIdent f k
>             infos = qualLookupVar (qualifyWith m f) env
>             left  = Left  (f', FunLhs f' ts)
>             right = Right $ ConstructorPattern (qualify f) ts
>     OpLhs t1 op t2
>       | not $ isDataConstr op env -> return left
>       | k /= globalScopeId        -> return right
>       | null infos                -> return left
>       | otherwise                 -> do report $ errToplevelPattern p
>                                         return right
>       where op'   = renameIdent op k
>             infos = qualLookupVar (qualifyWith m op) env
>             left  = Left (op', OpLhs t1 op' t2)
>             right = checkOpLhs k env (infixPattern t1 (qualify op)) t2
>             infixPattern (InfixPattern t1' op1 t2') op2 t3 =
>               InfixPattern t1' op1 (infixPattern t2' op2 t3)
>             infixPattern t1' op1 t2' = InfixPattern t1' op1 t2'
>     ApLhs lhs ts -> do
>       checked <- checkEqLhs p lhs
>       case checked of
>         Left (f', lhs') -> return $ Left (f', ApLhs lhs' ts)
>         r               -> do report $ errNonVariable "curried definition" f
>                               return $ r
>         where (f, _) = flatLhs lhs

> checkOpLhs :: Integer -> RenameEnv -> (ConstrTerm -> ConstrTerm)
>            -> ConstrTerm -> Either (Ident, Lhs) ConstrTerm
> checkOpLhs k env f (InfixPattern t1 op t2)
>   | isJust m || isDataConstr op' env
>   = checkOpLhs k env (f . InfixPattern t1 op) t2
>   | otherwise
>   = Left (op'', OpLhs (f t1) op'' t2)
>   where (m,op') = (qualidMod op, qualidId op)
>         op''    = renameIdent op' k
> checkOpLhs _ _ f t = Right (f t)

-- ---------------------------------------------------------------------------

> joinEquations :: [Decl] -> SCM [Decl]
> joinEquations [] = return []
> joinEquations (FunctionDecl p f eqs : FunctionDecl _ f' [eq] : ds)
>   | f == f' = do
>     when (getArity (head eqs) /= getArity eq) $ report $ errDifferentArity f
>     joinEquations (FunctionDecl p f (eqs ++ [eq]) : ds)
>   where getArity = length . snd . getFlatLhs
> joinEquations (d : ds) = (d :) `liftM` joinEquations ds

> checkDecls :: (Decl -> RenameEnv -> RenameEnv) -> [Decl] -> SCM [Decl]
> checkDecls bindDecl ds = do
>   let dbls@[dblVar, dblTys, dblEAs] = map findDouble [bvs, tys, evs]
>   onJust (report . errDuplicateDefinition) dblVar
>   onJust (report . errDuplicateTypeSig   ) dblTys
>   onJust (report . errDuplicateEvalAnnot ) dblEAs
>   let missingTy = [f | FlatExternalDecl _ fs' <- ds, f <- fs', f `notElem` tys]
>   mapM_ (report . errNoTypeSig) missingTy
>   if all isNothing dbls && null missingTy
>     then do
>       modifyRenameEnv $ \env -> foldr bindDecl env (tds ++ vds)
>       mapM (checkDeclRhs bvs) ds
>     else return ds -- skip further checking
>   where vds    = filter isValueDecl ds
>         tds    = filter isTypeSig ds
>         bvs    = concatMap vars vds
>         tys    = concatMap vars tds
>         evs    = concatMap vars $ filter isEvalAnnot ds
>         onJust = maybe (return ())

-- ---------------------------------------------------------------------------

> checkDeclRhs :: [Ident] -> Decl -> SCM Decl
> checkDeclRhs bvs (TypeSig      p vs ty) =
>   (\vs' -> TypeSig p vs' ty) `liftM` mapM (checkLocalVar bvs) vs
> checkDeclRhs bvs (EvalAnnot    p vs ev) =
>   (\vs' -> EvalAnnot p vs' ev) `liftM` mapM (checkLocalVar bvs) vs
> checkDeclRhs _   (FunctionDecl p f eqs) =
>   FunctionDecl p f `liftM` mapM checkEquation eqs
> checkDeclRhs _   (PatternDecl  p t rhs) =
>   PatternDecl p t `liftM` checkRhs rhs
> checkDeclRhs _   d                      = return d

> checkLocalVar :: [Ident] -> Ident -> SCM Ident
> checkLocalVar bvs v = do
>   when (v `notElem` bvs) $ report $ errNoBody v
>   return v

> checkEquation :: Equation -> SCM Equation
> checkEquation (Equation p lhs rhs) = inNestedScope $ do
>   lhs' <- checkLhs p lhs >>= addBoundVariables
>   rhs' <- checkRhs rhs
>   return $ Equation p lhs' rhs'

> checkLhs :: Position -> Lhs -> SCM Lhs
> checkLhs p (FunLhs    f ts) = FunLhs f `liftM` mapM (checkConstrTerm p) ts
> checkLhs p (OpLhs t1 op t2) = do
>   let wrongCalls = concatMap (checkParenConstrTerm (Just $ qualify op)) [t1,t2]
>   unless (null wrongCalls) $ report $ errInfixWithoutParens
>     (positionOfIdent op) wrongCalls
>   liftM2 (flip OpLhs op) (checkConstrTerm p t1) (checkConstrTerm p t2)
> checkLhs p (ApLhs   lhs ts) =
>   liftM2 ApLhs (checkLhs p lhs) (mapM (checkConstrTerm p) ts)

checkParen
@param Aufrufende InfixFunktion
@param ConstrTerm
@return Liste mit fehlerhaften Funktionsaufrufen
\begin{verbatim}

> checkParenConstrTerm :: (Maybe QualIdent) -> ConstrTerm -> [(QualIdent,QualIdent)]
> checkParenConstrTerm _ (LiteralPattern          _) = []
> checkParenConstrTerm _ (NegativePattern       _ _) = []
> checkParenConstrTerm _ (VariablePattern         _) = []
> checkParenConstrTerm _ (ConstructorPattern   _ cs) =
>   concatMap (checkParenConstrTerm Nothing) cs
> checkParenConstrTerm o (InfixPattern     t1 op t2) =
>   maybe [] (\c -> [(c, op)]) o
>   ++ checkParenConstrTerm Nothing t1 ++ checkParenConstrTerm Nothing t2
> checkParenConstrTerm _ (ParenPattern            t) =
>   checkParenConstrTerm Nothing t
> checkParenConstrTerm _ (TuplePattern         _ ts) =
>   concatMap (checkParenConstrTerm Nothing) ts
> checkParenConstrTerm _ (ListPattern          _ ts) =
>   concatMap (checkParenConstrTerm Nothing) ts
> checkParenConstrTerm o (AsPattern             _ t) =
>   checkParenConstrTerm o t
> checkParenConstrTerm o (LazyPattern           _ t) =
>   checkParenConstrTerm o t
> checkParenConstrTerm _ (FunctionPattern      _ ts) =
>   concatMap (checkParenConstrTerm Nothing) ts
> checkParenConstrTerm o (InfixFuncPattern t1 op t2) =
>   maybe [] (\c -> [(c, op)]) o
>   ++ checkParenConstrTerm Nothing t1 ++ checkParenConstrTerm Nothing t2
> checkParenConstrTerm _ (RecordPattern        fs t) =
>     maybe [] (checkParenConstrTerm Nothing) t
>     ++ concatMap (\(Field _ _ t') -> checkParenConstrTerm Nothing t') fs

> checkConstrTerm :: Position -> ConstrTerm -> SCM ConstrTerm
> checkConstrTerm _ (LiteralPattern        l) =
>   LiteralPattern `liftM` renameLiteral l
> checkConstrTerm _ (NegativePattern    op l) =
>   NegativePattern op `liftM` renameLiteral l
> checkConstrTerm p (VariablePattern       v)
>   | v == anonId = (VariablePattern . renameIdent v) `liftM` newId
>   | otherwise   = checkConstructorPattern p (qualify v) []
> checkConstrTerm p (ConstructorPattern c ts) =
>   checkConstructorPattern p c ts
> checkConstrTerm p (InfixPattern   t1 op t2) =
>   checkInfixPattern p t1 op t2
> checkConstrTerm p (ParenPattern          t) =
>   ParenPattern `liftM` checkConstrTerm p t
> checkConstrTerm p (TuplePattern     pos ts) =
>   TuplePattern pos `liftM` mapM (checkConstrTerm p) ts
> checkConstrTerm p (ListPattern      pos ts) =
>   ListPattern pos `liftM` mapM (checkConstrTerm p) ts
> checkConstrTerm p (AsPattern           v t) = do
>   liftM2 AsPattern (checkVar "@ pattern" v) (checkConstrTerm p t)
> checkConstrTerm p (LazyPattern       pos t) =
>   LazyPattern pos `liftM` checkConstrTerm p t
> checkConstrTerm p (RecordPattern      fs t) =
>   checkRecordPattern p fs t
> checkConstrTerm _ (FunctionPattern     _ _) = internalError $
>   "SyntaxCheck.checkConstrTerm: function pattern not defined"
> checkConstrTerm _ (InfixFuncPattern  _ _ _) = internalError $
>   "SyntaxCheck.checkConstrTerm: infix function pattern not defined"

> checkConstructorPattern :: Position -> QualIdent -> [ConstrTerm]
>                         -> SCM ConstrTerm
> checkConstructorPattern p c ts = do
>   env <- getRenameEnv
>   m <- getModuleIdent
>   k <- getScopeId
>   case qualLookupVar c env of
>     [Constr n] -> processCons c n
>     [r]        -> processVarFun r k
>     rs -> case qualLookupVar (qualQualify m c) env of
>       [Constr n] -> processCons (qualQualify m c) n
>       [r]        -> processVarFun r k
>       []
>         | null ts && not (isQualified c) ->
>             return (VariablePattern (renameIdent (unqualify c) k))
>         | null rs -> do
>             report $ errUndefinedData c
>             return $ ConstructorPattern c ts
>       _ -> do report $ errAmbiguousData c
>               return $ ConstructorPattern c ts
>   where
>   n' = length ts
>   processCons qc n = do
>     when (n /= n') $ report $ errWrongArity c n n'
>     ConstructorPattern qc `liftM` mapM (checkConstrTerm p) ts
>   processVarFun r k = do
>     let n = arity r
>     if null ts && not (isQualified c)
>       then return $ VariablePattern $ renameIdent (varIdent r) k
>       else do
>         checkFuncPatsExtension p
>         ts' <- mapM (checkConstrTerm p) ts
>         if n' > n
>           then let (ts1, ts2) = splitAt n ts'
>                in  return $ genFuncPattAppl
>                    (FunctionPattern (qualVarIdent r) ts1) ts2
>           else return $ FunctionPattern (qualVarIdent r) ts'

> checkInfixPattern :: Position -> ConstrTerm -> QualIdent -> ConstrTerm
>                   -> SCM ConstrTerm
> checkInfixPattern p t1 op t2 = do
>   m <- getModuleIdent
>   env <- getRenameEnv
>   case qualLookupVar op env of
>     [Constr n] -> infixPattern op n
>     [_]        -> funcPattern  op
>     rs         -> case qualLookupVar (qualQualify m op) env of
>       [Constr n]   -> infixPattern (qualQualify m op) n
>       [_]          -> funcPattern  (qualQualify m op)
>       rs'          -> do if (null rs && null rs')
>                             then report $ errUndefinedData op
>                             else report $ errAmbiguousData op
>                          return $ InfixPattern t1 op t2
>   where
>   infixPattern qop n = do
>     when (n /= 2) $ report $ errWrongArity op n 2
>     liftM2 (flip InfixPattern qop) (checkConstrTerm p t1)
>                                    (checkConstrTerm p t2)
>   funcPattern qop = do
>     checkFuncPatsExtension p
>     liftM2 (flip InfixFuncPattern qop) (checkConstrTerm p t1)
>                                        (checkConstrTerm p t2)



> checkRecordPattern :: Position -> [Field ConstrTerm]
>                    -> (Maybe ConstrTerm) -> SCM ConstrTerm
> checkRecordPattern p fs t = do
>   checkRecordExtension p
>   case fs of
>     [] -> do report (errEmptyRecord p)
>              return (RecordPattern fs t)
>     (Field _ l _ : _) -> do
>     env <- getRenameEnv
>     case lookupVar l env of
>       [RecordLabel r ls] -> do
>         when (isJust duplicate) $ report $ errDuplicateLabel
>                                          $ fromJust duplicate
>         if isNothing t
>           then do
>             when (not $ null missings) $ report $ errMissingLabel
>               (positionOfIdent l) (head missings) r "record pattern"
>             flip RecordPattern t `liftM` mapM (checkFieldPatt r) fs
>           else if t == Just (VariablePattern anonId)
>             then liftM2 RecordPattern
>                         (mapM (checkFieldPatt r) fs)
>                         (Just `liftM` checkConstrTerm p (fromJust t))
>             else do report (errIllegalRecordPattern p)
>                     return $ RecordPattern fs t
>         where ls'       = map fieldLabel fs
>               duplicate = findDouble ls'
>               missings  = ls \\ ls'
>       [] -> report (errUndefinedLabel l) >> return (RecordPattern fs t)
>       [_] -> report (errNotALabel l) >> return (RecordPattern fs t)
>       _   -> report (errDuplicateDefinition l) >> return (RecordPattern fs t)

> checkFieldPatt :: QualIdent -> Field ConstrTerm -> SCM (Field ConstrTerm)
> checkFieldPatt r (Field p l t) = do
>   env <- getRenameEnv
>   case lookupVar l env of
>     [RecordLabel r' _] -> when (r /= r') $ report $ errIllegalLabel l r
>     []                 -> report $ errUndefinedLabel l
>     [_]                -> report $ errNotALabel l
>     _                  -> report $ errDuplicateDefinition l
>   Field p l `liftM` checkConstrTerm (positionOfIdent l) t

> -- Note: process decls first
> checkRhs :: Rhs -> SCM Rhs
> checkRhs (SimpleRhs p e ds) = inNestedScope $ liftM2 (flip (SimpleRhs p))
>   (checkDeclGroup bindVarDecl ds) (checkExpr p e)
> checkRhs (GuardedRhs es ds) = inNestedScope $ liftM2 (flip GuardedRhs)
>   (checkDeclGroup bindVarDecl ds) (mapM checkCondExpr es)

> checkCondExpr :: CondExpr -> SCM CondExpr
> checkCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (checkExpr p g) (checkExpr p e)

> checkExpr :: Position -> Expression -> SCM Expression
> checkExpr _ (Literal     l) = Literal       `liftM` renameLiteral l
> checkExpr _ (Variable    v) = checkVariable v
> checkExpr _ (Constructor c) = checkVariable c
> checkExpr p (Paren       e) = Paren         `liftM` checkExpr p e
> checkExpr p (Typed    e ty) = flip Typed ty `liftM` checkExpr p e
> checkExpr p (Tuple  pos es) = Tuple pos     `liftM` mapM (checkExpr p) es
> checkExpr p (List   pos es) = List pos      `liftM` mapM (checkExpr p) es
> checkExpr p (ListCompr      pos e qs) = withLocalEnv $
>   -- Note: must be flipped to insert qs into RenameEnv first
>   liftM2 (flip (ListCompr pos)) (mapM (checkStatement p) qs) (checkExpr p e)
> checkExpr p (EnumFrom              e) = EnumFrom `liftM` checkExpr p e
> checkExpr p (EnumFromThen      e1 e2) =
>   liftM2 EnumFromThen (checkExpr p e1) (checkExpr p e2)
> checkExpr p (EnumFromTo        e1 e2) =
>   liftM2 EnumFromTo (checkExpr p e1) (checkExpr p e2)
> checkExpr p (EnumFromThenTo e1 e2 e3) =
>   liftM3 EnumFromThenTo (checkExpr p e1) (checkExpr p e2) (checkExpr p e3)
> checkExpr p (UnaryMinus         op e) = UnaryMinus op `liftM` checkExpr p e
> checkExpr p (Apply             e1 e2) =
>   liftM2 Apply (checkExpr p e1) (checkExpr p e2)
> checkExpr p (InfixApply     e1 op e2) =
>   liftM3 InfixApply (checkExpr p e1) (checkOp op) (checkExpr p e2)
> checkExpr p (LeftSection        e op) =
>   liftM2 LeftSection (checkExpr p e) (checkOp op)
> checkExpr p (RightSection       op e) =
>   liftM2 RightSection (checkOp op) (checkExpr p e)
> checkExpr p (Lambda           r ts e) = inNestedScope $
>   liftM2 (Lambda r) (mapM (checkPattern p) ts) (checkExpr p e)
> checkExpr p (Let                ds e) = inNestedScope $
>   liftM2 Let (checkDeclGroup bindVarDecl ds) (checkExpr p e)
> checkExpr p (Do                sts e) = withLocalEnv $
>   liftM2 Do (mapM (checkStatement p) sts) (checkExpr p e)
> checkExpr p (IfThenElse r e1 e2 e3) =
>   liftM3 (IfThenElse r) (checkExpr p e1) (checkExpr p e2) (checkExpr p e3)
> checkExpr p (Case r e alts) =
>   liftM2 (Case r) (checkExpr p e) (mapM checkAlt alts)
> checkExpr p rec@(RecordConstr   fs) = do
>   checkRecordExtension p
>   env <- getRenameEnv
>   case fs of
>     []              -> report (errEmptyRecord p) >> return rec
>     Field _ l _ : _ -> case lookupVar l env of
>       [RecordLabel r ls] -> do
>         unless (null dups)     $ report $ errDuplicateLabel $ head dups
>         unless (null missings) $ report $ errMissingLabel
>              (positionOfIdent l) (head missings) r "record construction"
>         RecordConstr `liftM` mapM (checkFieldExpr r) fs
>         where ls' = map fieldLabel fs
>               dups = maybeToList (findDouble ls')
>               missings = ls \\ ls'
>       []  -> report (errUndefinedLabel l)      >> return rec
>       [_] -> report (errNotALabel l)           >> return rec
>       _   -> report (errDuplicateDefinition l) >> return rec

> checkExpr p (RecordSelection e l) = do
>   checkRecordExtension p
>   env <- getRenameEnv
>   case lookupVar l env of
>     [RecordLabel _ _] -> return ()
>     []                -> report $ errUndefinedLabel l
>     [_]               -> report $ errNotALabel l
>     _                 -> report $ errDuplicateDefinition l
>   flip RecordSelection l `liftM` checkExpr p e
> checkExpr p rec@(RecordUpdate fs e) = do
>   checkRecordExtension p
>   env <- getRenameEnv
>   case fs of
>     []              -> report (errEmptyRecord p) >> return rec
>     Field _ l _ : _ -> case lookupVar l env of
>       [RecordLabel r _] -> do
>         unless (null dups) $ report $ errDuplicateLabel $ head dups
>         liftM2 RecordUpdate (mapM (checkFieldExpr r) fs)
>                             (checkExpr (positionOfIdent l) e)
>         where dups = maybeToList $ findDouble $ map fieldLabel fs
>       []  -> report (errUndefinedLabel l)      >> return rec
>       [_] -> report (errNotALabel l)           >> return rec
>       _   -> report (errDuplicateDefinition l) >> return rec

> checkVariable :: QualIdent -> SCM Expression
> checkVariable v
>   | unqualify v == anonId = do
>     checkAnonFreeVarsExtension $ positionOfQualIdent v
>     return $ Variable v
>   | otherwise             = do
>     env <- getRenameEnv
>     case qualLookupVar v env of
>       []              -> do report $ errUndefinedVariable v
>                             return $ Variable v
>       [Constr _]      -> return $ Constructor v
>       [GlobalVar _ _] -> return $ Variable v
>       [LocalVar _ v'] -> return $ Variable $ qualify v'
>       rs -> do
>         m <- getModuleIdent
>         case qualLookupVar (qualQualify m v) env of
>           []              -> do report $ errAmbiguousIdent rs v
>                                 return $ Variable v
>           [Constr _]      -> return $ Constructor v
>           [GlobalVar _ _] -> return $ Variable v
>           [LocalVar _ v'] -> return $ Variable $ qualify v'
>           rs'             -> do report $ errAmbiguousIdent rs' v
>                                 return $ Variable v

> -- * Because patterns or decls eventually introduce new variables, the
> --   scope has to be nested one level.
> -- * Because statements are processed list-wise, inNestedEnv can not be
> --   used as this nesting must be visible to following statements.
> checkStatement :: Position -> Statement -> SCM Statement
> checkStatement p (StmtExpr   pos e) = StmtExpr pos `liftM` checkExpr p e
> checkStatement p (StmtBind pos t e) =
>   liftM2 (flip (StmtBind pos)) (checkExpr p e) (incNesting >> checkPattern p t)
> checkStatement _ (StmtDecl      ds) =
>   StmtDecl `liftM` (incNesting >> checkDeclGroup bindVarDecl ds)

> checkPattern :: Position -> ConstrTerm -> SCM ConstrTerm
> checkPattern p t = checkConstrTerm p t >>= addBoundVariables

> checkOp :: InfixOp -> SCM InfixOp
> checkOp op = do
>   env <- getRenameEnv
>   case qualLookupVar v env of
>     []              -> report (errUndefinedVariable v) >> return op
>     [Constr _]      -> return $ InfixConstr v
>     [GlobalVar _ _] -> return $ InfixOp v
>     [LocalVar _ v'] -> return $ InfixOp $ qualify v'
>     rs              -> do
>       m <- getModuleIdent
>       case qualLookupVar (qualQualify m v) env of
>         []              -> report (errAmbiguousIdent rs v) >> return op
>         [Constr _]      -> return $ InfixConstr v
>         [GlobalVar _ _] -> return $ InfixOp v
>         [LocalVar _ v'] -> return $ InfixOp $ qualify v'
>         rs'             -> report (errAmbiguousIdent rs' v) >> return op
>   where v = opName op

> checkAlt :: Alt -> SCM Alt
> checkAlt (Alt p t rhs) = inNestedScope $
>   liftM2 (Alt p) (checkPattern p t) (checkRhs rhs)

> addBoundVariables :: QuantExpr t => t -> SCM t
> addBoundVariables ts = do
>   case findDouble bvs of
>     Nothing -> modifyRenameEnv $ \ env -> foldr bindVar env bvs
>     Just v  -> report $ errDuplicateVariable v
>   return ts
>   where bvs = bv ts

> checkFieldExpr :: QualIdent -> Field Expression -> SCM (Field Expression)
> checkFieldExpr r (Field p l e) = do
>   env <- getRenameEnv
>   case lookupVar l env of
>     [RecordLabel r' _] -> when (r /= r') $ report $ errIllegalLabel l r
>     []                 -> report $ errUndefinedLabel l
>     [_]                -> report $ errNotALabel l
>     _                  -> report $ errDuplicateDefinition l
>   Field p l `liftM` checkExpr (positionOfIdent l) e

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrs :: Decl -> [Ident]
> constrs (DataDecl _ _ _ cs) = map constr cs
>   where constr (ConstrDecl   _ _ c _) = c
>         constr (ConOpDecl _ _ _ op _) = op
> constrs (NewtypeDecl _ _ _ (NewConstrDecl _ _ c _)) = [c]
> constrs _ = []

> vars :: Decl -> [Ident]
> vars (TypeSig         _ fs _) = fs
> vars (EvalAnnot       _ fs _) = fs
> vars (FunctionDecl     _ f _) = [f]
> vars (ExternalDecl _ _ _ f _) = [f]
> vars (FlatExternalDecl  _ fs) = fs
> vars (PatternDecl      _ t _) = bv t
> vars (ExtraVariables    _ vs) = vs
> vars _ = []

> renameLiteral :: Literal -> SCM Literal
> renameLiteral (Int v i) = liftM (flip Int i . renameIdent v) newId
> renameLiteral l = return l

Since the compiler expects all rules of the same function to be together,
it is necessary to sort the list of declarations.

> sortFuncDecls :: [Decl] -> [Decl]
> sortFuncDecls decls = sortFD Set.empty [] decls
>  where
>  sortFD _   res []              = reverse res
>  sortFD env res (decl : decls') = case decl of
>    FunctionDecl _ ident _
>     | ident `Set.member` env
>     -> sortFD env (insertBy cmpFuncDecl decl res) decls'
>     | otherwise
>     -> sortFD (Set.insert ident env) (decl:res) decls'
>    _    -> sortFD env (decl:res) decls'

> cmpFuncDecl :: Decl -> Decl -> Ordering
> cmpFuncDecl (FunctionDecl _ id1 _) (FunctionDecl _ id2 _)
>    | id1 == id2 = EQ
>    | otherwise  = GT
> cmpFuncDecl _ _ = GT

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
> isConstr (Constr        _) = True
> isConstr (GlobalVar   _ _) = False
> isConstr (LocalVar    _ _) = False
> isConstr (RecordLabel _ _) = False

> varIdent :: RenameInfo -> Ident
> varIdent (GlobalVar _ v) = unqualify v
> varIdent (LocalVar  _ v) = v
> varIdent _ = internalError "SyntaxCheck.varIdent: no variable"

> qualVarIdent :: RenameInfo -> QualIdent
> qualVarIdent (GlobalVar _ v) = v
> qualVarIdent (LocalVar  _ v) = qualify v
> qualVarIdent _ = internalError "SyntaxCheck.qualVarIdent: no variable"

> arity :: RenameInfo -> Int
> arity (Constr         n) = n
> arity (GlobalVar   n  _) = n
> arity (LocalVar    n  _) = n
> arity (RecordLabel _ ls) = length ls

\end{verbatim}
Unlike expressions, constructor terms have no possibility to represent
over-applications in functional patterns. Therefore it is necessary to
transform them to nested function patterns using the prelude function
\texttt{apply}. E.g., the function pattern \texttt{(id id 10)} is transformed
to \texttt{(apply (id id) 10)}.
\begin{verbatim}

> genFuncPattAppl :: ConstrTerm -> [ConstrTerm] -> ConstrTerm
> genFuncPattAppl term []     = term
> genFuncPattAppl term (t:ts)
>    = FunctionPattern qApplyId [genFuncPattAppl term ts, t]
>  where
>  qApplyId = qualifyWith preludeMIdent (mkIdent "apply")

\end{verbatim}
Miscellaneous functions.
\begin{verbatim}

> checkFuncPatsExtension :: Position -> SCM ()
> checkFuncPatsExtension p = checkExtension p
>   "Functional Patterns" FunctionalPatterns

> checkRecordExtension :: Position -> SCM ()
> checkRecordExtension p = checkExtension p "Records" Records

> checkAnonFreeVarsExtension :: Position -> SCM ()
> checkAnonFreeVarsExtension p = checkExtension p
>   "Anonymous free variables" AnonFreeVars

> checkExtension :: Position -> String -> Extension -> SCM ()
> checkExtension pos msg ext = do
>   enabled <- hasExtension ext
>   unless enabled $ do
>     report $ errMissingLanguageExtension pos msg ext
>     enableExtension ext

> typeArity :: TypeExpr -> Int
> typeArity (ArrowType _ t2) = 1 + typeArity t2
> typeArity _                = 0

> getFlatLhs :: Equation -> (Ident, [ConstrTerm])
> getFlatLhs (Equation  _ lhs _) = flatLhs lhs

\end{verbatim}
Error messages.
\begin{verbatim}

> errUndefinedVariable :: QualIdent -> Message
> errUndefinedVariable v = qposErr v $ qualName v ++ " is undefined"

> errUndefinedData :: QualIdent -> Message
> errUndefinedData c = qposErr c $ "Undefined data constructor " ++ qualName c

> errUndefinedLabel :: Ident -> Message
> errUndefinedLabel l = posErr l $ "Undefined record label `" ++ name l ++ "`"

> errAmbiguousIdent :: [RenameInfo] -> QualIdent -> Message
> errAmbiguousIdent rs | any isConstr rs = errAmbiguousData
>                      | otherwise       = errAmbiguousVariable

> errAmbiguousVariable :: QualIdent -> Message
> errAmbiguousVariable v = qposErr v $ "Ambiguous variable " ++ qualName v

> errAmbiguousData :: QualIdent -> Message
> errAmbiguousData c = qposErr c $ "Ambiguous data constructor " ++ qualName c

> errDuplicateDefinition :: Ident -> Message
> errDuplicateDefinition v = posErr v $
>   "More than one definition for `" ++ name v ++ "`"

> errDuplicateVariable :: Ident -> Message
> errDuplicateVariable v = posErr v $
>   name v ++ " occurs more than once in pattern"

> errMultipleDataConstructor :: [Ident] -> Message
> errMultipleDataConstructor [] = internalError
>   "SyntaxCheck.errMultipleDataDeclaration: empty list"
> errMultipleDataConstructor (i:is) = posErr i $
>   "Multiple definitions for data constructor `" ++ name i ++ "` at:\n"
>   ++ unlines (map showPos (i:is))
>   where showPos = ("    " ++) . showLine . positionOfIdent

> errDuplicateTypeSig :: Ident -> Message
> errDuplicateTypeSig v = posErr v $
>   "More than one type signature for `" ++ name v ++ "`"

> errDuplicateEvalAnnot :: Ident -> Message
> errDuplicateEvalAnnot v = posErr v $
>   "More than one eval annotation for `" ++ name v ++ "`"

> errDuplicateLabel :: Ident -> Message
> errDuplicateLabel l = posErr l $
>   "Multiple occurrence of record label `" ++ name l ++ "`"

> errMissingLabel :: Position -> Ident -> QualIdent -> String -> Message
> errMissingLabel p l r what = toMessage p $
>   "Missing label `" ++ name l
>   ++ "` in the " ++ what ++ " of `" ++ name (unqualify r) ++ "`"

> errIllegalLabel :: Ident -> QualIdent -> Message
> errIllegalLabel l r = posErr l $
>   "Label `" ++ name l ++ "` is not defined in record `"
>   ++ name (unqualify r) ++ "`"

> errIllegalRecordId :: Ident -> Message
> errIllegalRecordId r = posErr r $ "Record identifier `" ++ name r
>     ++ "` already assigned to a data constructor"

> errNonVariable :: String -> Ident -> Message
> errNonVariable what c = posErr c $
>   "Data constructor `" ++ name c ++ "` in left hand side of " ++ what

> errNoBody :: Ident -> Message
> errNoBody v = posErr v $ "No body for `" ++ name v ++ "`"

> errNoTypeSig :: Ident -> Message
> errNoTypeSig f = posErr f $
>   "No type signature for external function `" ++ name f ++ "`"

> errToplevelPattern :: Position -> Message
> errToplevelPattern p = toMessage p
>   "Pattern declaration not allowed at top-level"

> errNotALabel :: Ident -> Message
> errNotALabel l = posErr l $ "`" ++ name l ++ "` is not a record label"

> errDifferentArity :: Ident -> Message
> errDifferentArity f = posErr f $
>   "Equations for `" ++ name f ++ "` have different arities"

> errWrongArity :: QualIdent -> Int -> Int -> Message
> errWrongArity c arity' argc = qposErr c $
>   "Data constructor " ++ qualName c ++ " expects " ++ arguments arity' ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> errIllegalRecordPattern :: Position -> Message
> errIllegalRecordPattern p = toMessage p
>   "Expexting `_` after `|` in the record pattern"

> errMissingLanguageExtension :: Position -> String -> Extension -> Message
> errMissingLanguageExtension p what ext = toMessage p $
>   what ++ " are not supported in standard Curry."
>   ++ "\n  Use flag -e or -X" ++ show ext ++ " to enable this extension."

> errEmptyRecord :: Position -> Message
> errEmptyRecord p = toMessage p "empty records are not allowed"

> errInfixWithoutParens :: Position -> [(QualIdent, QualIdent)] -> Message
> errInfixWithoutParens p calls = toMessage p $
>   "Missing parens in infix patterns: \n" ++ unlines (map showCall calls)
>   where showCall (q1, q2) =
>           show q1 ++ " " ++ showLine (positionOfQualIdent q1)
>           ++ "calls " ++ show q2 ++ " " ++ showLine (positionOfQualIdent q2)

\end{verbatim}
