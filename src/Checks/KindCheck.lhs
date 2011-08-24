% $Id: KindCheck.lhs,v 1.33 2004/02/13 19:24:04 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{KindCheck.lhs}
\section{Checking Type Definitions}
After the source file has been parsed and all modules have been
imported, the compiler first performs kind checking on all type
definitions and signatures. Because Curry currently does not support
type classes, kind checking is rather trivial. All types must be of
first order kind ($\star$), i.e., all type constructor applications
must be saturated.

During kind checking, this module will also disambiguate nullary
constructors and type variables which -- in contrast to Haskell -- is
not possible on purely syntactic criteria. In addition it is checked
that all type constructors and type variables occurring on the right
hand side of a type declaration are actually defined and no identifier
is defined more than once.
\begin{verbatim}

> module Checks.KindCheck (kindCheck) where

> import Control.Monad.State

> import Curry.Base.Position
> import Curry.Base.Ident
> import Curry.Base.MessageMonad (Message (..), showError)
> import Curry.Syntax

> import Base.Messages (errorAt', internalError)
> import Base.Utils (findDouble)

> import Env.TopEnv
> import Env.TypeConstructors (TCEnv, tcArity)

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment containing the kind information for all type
constructors. The function \texttt{kindCheck} first initializes this
environment by filtering out the arity of each type constructor from
the imported type environment. Next, the arities of all locally
defined type constructors are inserted into the environment, and,
finally, the declarations are checked within this environment.
\begin{verbatim}

TODO: Propagate errors

> kindCheck :: ModuleIdent -> TCEnv -> [Decl] -> [Decl]
> kindCheck m tcEnv decls = case findDouble $ map typeConstr typeDecls of
>   Just tc -> errorAt' $ errDuplicateType tc
>   Nothing -> case errors s' of
>     []   -> decls'
>     errs -> errorAt' $ last errs
>   where typeDecls = filter isTypeDecl decls
>         kEnv      = foldr (bindKind m) (fmap tcArity tcEnv) typeDecls
>         initState = CheckState m kEnv []
>         (decls',s') = runKcM (mapM checkDecl decls) initState

> data CheckState = CheckState
>   { moduleIdent :: ModuleIdent
>   , kindEnv     :: KindEnv
>   , errors      :: [(Position, String)]
>   }

> type KcM = State CheckState

> runKcM :: KcM a -> CheckState -> (a, CheckState)
> runKcM = runState

> reportError :: (Position, String) -> KcM ()
> reportError err = modify (\ s -> s { errors = err : errors s })

\end{verbatim}
The kind environment only needs to record the arity of each type constructor.
\begin{verbatim}

> type KindEnv = TopEnv Int

> bindKind :: ModuleIdent -> Decl -> KindEnv -> KindEnv
> bindKind m (DataDecl    _ tc tvs _) = bindKind' m tc tvs
> bindKind m (NewtypeDecl _ tc tvs _) = bindKind' m tc tvs
> bindKind m (TypeDecl    _ tc tvs _) = bindKind' m tc tvs
> bindKind _ _                        = id

> bindKind' :: ModuleIdent -> Ident -> [Ident] -> KindEnv -> KindEnv
> bindKind' m tc tvs = bindTopEnv     "KindCheck.bindKind'"  tc n
>                    . qualBindTopEnv "KindCheck.bindKind'" qtc n
>   where n   = length tvs
>         qtc = qualifyWith m tc

> lookupKind :: Ident -> KindEnv -> [Int]
> lookupKind = lookupTopEnv

> qualLookupKind :: QualIdent -> KindEnv -> [Int]
> qualLookupKind = qualLookupTopEnv

\end{verbatim}
When type declarations are checked, the compiler will allow anonymous
type variables on the left hand side of the declaration, but not on
the right hand side. Function and pattern declarations must be
traversed because they can contain local type signatures.
\begin{verbatim}

> checkDecl :: Decl -> KcM Decl
> checkDecl (DataDecl      p tc tvs cs) = do
>   tvs' <- checkTypeLhs tvs
>   cs'  <- mapM (checkConstrDecl tvs') cs
>   return $ DataDecl p tc tvs' cs'
> checkDecl (NewtypeDecl   p tc tvs nc) = do
>   tvs' <- checkTypeLhs tvs
>   nc'  <- checkNewConstrDecl tvs' nc
>   return $ NewtypeDecl p tc tvs' nc'
> checkDecl (TypeDecl      p tc tvs ty) = do
>   tvs' <- checkTypeLhs tvs
>   ty'  <- checkClosedType tvs' ty
>   return $ TypeDecl p tc tvs' ty'
> checkDecl (TypeSig           p vs ty) = do
>   ty' <- checkType ty
>   return $ TypeSig p vs ty'
> checkDecl (FunctionDecl      p f eqs) = do
>   eqs' <- mapM checkEquation eqs
>   return $ FunctionDecl p f eqs'
> checkDecl (PatternDecl       p t rhs) = do
>   rhs' <- checkRhs rhs
>   return $ PatternDecl p t rhs'
> checkDecl (ExternalDecl p cc ie f ty) = do
>   ty' <- checkType ty
>   return $ ExternalDecl p cc ie f ty'
> checkDecl d                           = return d

> checkConstrDecl :: [Ident] -> ConstrDecl -> KcM ConstrDecl
> checkConstrDecl tvs (ConstrDecl p evs c tys) = do
>   evs' <- checkTypeLhs evs
>   tys' <- mapM (checkClosedType (evs' ++ tvs)) tys
>   return $ ConstrDecl p evs' c tys'
> checkConstrDecl tvs (ConOpDecl p evs ty1 op ty2) = do
>   evs' <- checkTypeLhs evs
>   let tvs' = evs' ++ tvs
>   ty1' <- checkClosedType tvs' ty1
>   ty2' <- checkClosedType tvs' ty2
>   return $ ConOpDecl p evs' ty1' op ty2'

> checkNewConstrDecl :: [Ident] -> NewConstrDecl -> KcM NewConstrDecl
> checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
>   evs' <- checkTypeLhs evs
>   ty'  <- checkClosedType (evs' ++ tvs) ty
>   return $ NewConstrDecl p evs' c ty'

> -- |Check the left-hand-side of a type declaration for
> -- * Anonymous type variables are allowed
> -- * only type variables (no type constructors)
> -- * linearity
> checkTypeLhs :: [Ident] -> KcM [Ident]
> checkTypeLhs []         = return []
> checkTypeLhs (tv : tvs) = do
>   when (tv /= anonId) $ do
>     isTyCons <- gets (not . null . lookupKind tv . kindEnv)
>     when isTyCons        $ reportError $ errNoVariable tv
>     when (tv `elem` tvs) $ reportError $ errNonLinear  tv
>   tvs' <- checkTypeLhs tvs
>   return $ tv : tvs'

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: Equation -> KcM Equation
> checkEquation (Equation p lhs rhs) = do
>   rhs' <- checkRhs rhs
>   return $ Equation p lhs rhs'

> checkRhs :: Rhs -> KcM Rhs
> checkRhs (SimpleRhs p e ds) = do
>   e'  <- checkExpr e
>   ds' <- mapM checkDecl ds
>   return $ SimpleRhs p e' ds'
> checkRhs (GuardedRhs es ds) = do
>   es' <- mapM checkCondExpr es
>   ds' <- mapM checkDecl ds
>   return $ GuardedRhs es' ds'

> checkCondExpr :: CondExpr -> KcM CondExpr
> checkCondExpr (CondExpr p g e) = do
>   g' <- checkExpr g
>   e' <- checkExpr e
>   return $ CondExpr p g' e'

> checkExpr :: Expression -> KcM Expression
> checkExpr (Literal     l) = return $ Literal l
> checkExpr (Variable    v) = return $ Variable v
> checkExpr (Constructor c) = return $ Constructor c
> checkExpr (Paren       e) = do
>   e' <- checkExpr e
>   return $ Paren e'
> checkExpr (Typed    e ty) = do
>   e'  <- checkExpr e
>   ty' <- checkType ty
>   return $ Typed e' ty'
> checkExpr (Tuple    p es) = do
>   es' <- mapM checkExpr es
>   return $ Tuple p es'
> checkExpr (List     p es) = do
>   es' <- mapM checkExpr es
>   return $ List p es'
> checkExpr (ListCompr p e qs) = do
>   e'  <- checkExpr e
>   qs' <- mapM checkStmt qs
>   return $ ListCompr p e' qs'
> checkExpr (EnumFrom e) = do
>   e' <- checkExpr e
>   return $ EnumFrom e'
> checkExpr (EnumFromThen e1 e2) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   return $ EnumFromThen e1' e2'
> checkExpr (EnumFromTo e1 e2) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   return $ EnumFromTo e1' e2'
> checkExpr (EnumFromThenTo e1 e2 e3) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   e3' <- checkExpr e3
>   return $ EnumFromThenTo e1' e2' e3'
> checkExpr (UnaryMinus op e) = do
>   e' <- checkExpr e
>   return $ UnaryMinus op e'
> checkExpr (Apply e1 e2) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   return $ Apply e1' e2'
> checkExpr (InfixApply e1 op e2) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   return $ InfixApply e1' op e2'
> checkExpr (LeftSection e op) = do
>   e' <- checkExpr e
>   return $ LeftSection e' op
> checkExpr (RightSection op e) = do
>   e' <- checkExpr e
>   return $ RightSection op e'
> checkExpr (Lambda r ts e) = do
>   e' <- checkExpr e
>   return $ Lambda r ts e'
> checkExpr (Let ds e) = do
>   ds' <- mapM checkDecl ds
>   e'  <- checkExpr e
>   return $ Let ds' e'
> checkExpr (Do sts e) = do
>   sts' <- mapM checkStmt sts
>   e'   <- checkExpr e
>   return $ Do sts' e'
> checkExpr (IfThenElse r e1 e2 e3) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   e3' <- checkExpr e3
>   return $ IfThenElse r e1' e2' e3'
> checkExpr (Case r e alts) = do
>   e'    <- checkExpr e
>   alts' <- mapM checkAlt alts
>   return $ Case r e' alts'
> checkExpr (RecordConstr fs) = do
>   fs' <- mapM checkFieldExpr fs
>   return $ RecordConstr fs'
> checkExpr (RecordSelection e l) = do
>   e' <- checkExpr e
>   return $ RecordSelection e' l
> checkExpr (RecordUpdate fs e) = do
>   fs' <- mapM checkFieldExpr fs
>   e' <- checkExpr e
>   return $ RecordUpdate fs' e'

> checkStmt :: Statement -> KcM Statement
> checkStmt (StmtExpr   p e) = do
>   e' <- checkExpr e
>   return $ StmtExpr p e'
> checkStmt (StmtBind p t e) = do
>   e' <- checkExpr e
>   return $ StmtBind p t e'
> checkStmt (StmtDecl    ds) = do
>   ds' <- mapM checkDecl ds
>   return $ StmtDecl ds'

> checkAlt :: Alt -> KcM Alt
> checkAlt (Alt p t rhs) = do
>   rhs' <- checkRhs rhs
>   return $ Alt p t rhs'

> checkFieldExpr :: Field Expression -> KcM (Field Expression)
> checkFieldExpr (Field p l e) = do
>   e' <-  checkExpr e
>   return $ Field p l e'

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: [Ident] -> TypeExpr -> KcM TypeExpr
> checkClosedType tvs ty = checkType ty >>= checkClosed tvs

> checkType :: TypeExpr -> KcM TypeExpr
> checkType c@(ConstructorType tc tys) = do
>   m <- gets moduleIdent
>   kEnv <- gets kindEnv
>   case qualLookupKind tc kEnv of
>     []
>       | not (isQualified tc) && null tys -> return $ VariableType $ unqualify tc
>       | otherwise -> reportError (errUndefinedType tc) >> return c
>     [n]
>       | n  ==  n' -> do
>           tys' <- mapM checkType tys
>           return $ ConstructorType tc tys'
>       | otherwise -> reportError (errWrongArity tc n n') >> return c
>     _ -> case qualLookupKind (qualQualify m tc) kEnv of
>          [n]
>             | n  ==  n' -> do
>                 tys' <- mapM checkType tys
>                 return $ ConstructorType tc tys'
>             | otherwise -> reportError (errWrongArity tc n n') >> return c
>          _ -> reportError (errAmbiguousType tc) >> return c
>  where n' = length tys
> checkType (VariableType tv)
>   | tv == anonId = return $ VariableType tv
>   | otherwise    = checkType (ConstructorType (qualify tv) [])
> checkType (TupleType tys) = do
>   tys' <- mapM checkType tys
>   return $ TupleType tys'
> checkType (ListType ty) = do
>   ty' <- checkType ty
>   return $ ListType ty'
> checkType (ArrowType ty1 ty2) = do
>   ty1' <- checkType ty1
>   ty2' <- checkType ty2
>   return $ ArrowType ty1' ty2'
> checkType (RecordType fs r) = do
>   fs' <- mapM (\ (l, ty) -> do { ty' <- checkType ty; return (l, ty') }) fs
>   r'  <- case r of
>     Nothing -> return Nothing
>     Just ar -> Just `liftM` checkType ar
>   return $ RecordType fs' r'

> checkClosed :: [Ident] -> TypeExpr -> KcM TypeExpr
> checkClosed tvs (ConstructorType tc tys) = do
>   tys' <- mapM (checkClosed tvs) tys
>   return $ ConstructorType tc tys'
> checkClosed tvs (VariableType   tv) = do
>   when (tv == anonId || tv `notElem` tvs) $ reportError $ errUnboundVariable tv
>   return $ VariableType tv
> checkClosed tvs (TupleType     tys) = do
>   tys' <- mapM (checkClosed tvs) tys
>   return $ TupleType $ tys'
> checkClosed tvs (ListType       ty) = do
>   ty' <- checkClosed tvs ty
>   return $ ListType ty'
> checkClosed tvs (ArrowType ty1 ty2) = do
>   ty1' <- checkClosed tvs ty1
>   ty2' <- checkClosed tvs ty2
>   return $ ArrowType ty1' ty2'
> checkClosed tvs (RecordType   fs r) = do
>   fs' <- mapM (\ (l, ty) -> do { ty' <- checkClosed tvs ty; return (l, ty') }) fs
>   r'  <- case r of
>     Nothing -> return Nothing
>     Just ar -> Just `liftM` checkClosed tvs ar
>   return $ RecordType fs' r'

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> typeConstr :: Decl -> Ident
> typeConstr (DataDecl    _ tc _ _) = tc
> typeConstr (NewtypeDecl _ tc _ _) = tc
> typeConstr (TypeDecl    _ tc _ _) = tc
> typeConstr _ = internalError "KindCheck.typeConstr: no type declaration"

\end{verbatim}
Error messages:
\begin{verbatim}

> errUndefinedType :: QualIdent -> (Position, String)
> errUndefinedType tc = qposErr tc $ "Undefined type " ++ qualName tc

> errAmbiguousType :: QualIdent -> (Position, String)
> errAmbiguousType tc = qposErr tc $ "Ambiguous type " ++ qualName tc

> errDuplicateType :: Ident -> (Position, String)
> errDuplicateType tc = posErr tc
>                     $ "More than one definition for type " ++ name tc

> errNonLinear :: Ident -> (Position, String)
> errNonLinear tv = posErr tv $ "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> errNoVariable :: Ident -> (Position,String)
> errNoVariable tv = posErr tv $ "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> errWrongArity :: QualIdent -> Int -> Int -> (Position, String)
> errWrongArity tc arity argc = qposErr tc $
>   "Type constructor " ++ qualName tc ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> errUnboundVariable :: Ident -> (Position, String)
> errUnboundVariable tv = posErr tv $ "Unbound type variable " ++ name tv

> posErr :: Ident -> String -> (Position, String)
> posErr i errMsg = (positionOfIdent i, errMsg)

> qposErr :: QualIdent -> String -> (Position, String)
> qposErr i errMsg = (positionOfQualIdent i, errMsg)

\end{verbatim}
