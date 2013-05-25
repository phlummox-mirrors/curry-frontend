% $Id: KindCheck.lhs,v 1.33 2004/02/13 19:24:04 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% Modified by Björn Peemöller (bjp@informatik.uni-kiel.de)
%
\nwfilename{KindCheck.lhs}
\section{Checking Type Definitions}
After the source file has been parsed and all modules have been
imported, the compiler first performs kind checking on all type
definitions and signatures. Because Curry currently does not support
type classes, kind checking is rather trivial. All types must be of
first order kind ($\star$), i.e., all type constructor applications
must be saturated.

During kind checking, this module will also disambiguate nullary type
constructors and type variables which -- in contrast to Haskell -- is
not possible on purely syntactic criteria. In addition it is checked
that all type constructors and type variables occurring on the right
hand side of a type declaration are actually defined and no identifier
is defined more than once.
\begin{verbatim}

> module Checks.KindCheck (kindCheck) where

> import Control.Monad (forM, liftM, liftM2, liftM3, unless, when)
> import qualified Control.Monad.State as S (State, runState, gets, modify)
> import Text.PrettyPrint

> import Curry.Base.Ident
> import Curry.Base.Position
> import Curry.Syntax

> import Base.Messages (Message, posMessage, internalError)
> import Base.TopEnv
> import Base.Utils (findMultiples)

> import Env.TypeConstructor (TCEnv, tcArity)

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment containing the kind information for all type
constructors. The function \texttt{kindCheck} first initializes this
environment by filtering out the arity of each type constructor from
the imported type environment. Next, the arities of all locally
defined type constructors are inserted into the environment, and,
finally, the declarations are checked within this environment.
\begin{verbatim}

> kindCheck :: ModuleIdent -> TCEnv -> [Decl] -> ([Decl], [Message])
> kindCheck m tcEnv decls = case findMultiples $ map typeConstr tds of
>   [] -> runKCM (mapM checkDecl decls) initState
>   ms -> (decls, map errMultipleDeclaration ms)
>   where tds       = filter isTypeDecl decls
>         kEnv      = foldr (bindKind m) (fmap tcArity tcEnv) tds
>         initState = KCState m kEnv []

\end{verbatim}
The kind check monad.
\begin{verbatim}

> data KCState = KCState
>   { moduleIdent :: ModuleIdent
>   , kindEnv     :: KindEnv
>   , errors      :: [Message]
>   }

> type KCM = S.State KCState -- the Kind Check Monad

> runKCM :: KCM a -> KCState -> (a, [Message])
> runKCM kcm s = let (a, s') = S.runState kcm s in (a, reverse $ errors s')

> getModuleIdent :: KCM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> getKindEnv :: KCM KindEnv
> getKindEnv = S.gets kindEnv

> report :: Message -> KCM ()
> report err = S.modify (\ s -> s { errors = err : errors s })

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
> bindKind' m tc tvs = bindTopEnv     "KindCheck.bindKind'"  tc arity
>                    . qualBindTopEnv "KindCheck.bindKind'" qtc arity
>   where arity = length tvs
>         qtc   = qualifyWith m tc

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

> checkDecl :: Decl -> KCM Decl
> checkDecl (DataDecl     p tc tvs cs) = do
>   tvs' <- checkTypeLhs tvs
>   cs'  <- mapM (checkConstrDecl tvs') cs
>   return $ DataDecl p tc tvs' cs'
> checkDecl (NewtypeDecl  p tc tvs nc) = do
>   tvs' <- checkTypeLhs tvs
>   nc'  <- checkNewConstrDecl tvs' nc
>   return $ NewtypeDecl p tc tvs' nc'
> checkDecl (TypeDecl     p tc tvs ty) = do
>   tvs' <- checkTypeLhs tvs
>   ty'  <- checkClosedType tvs' ty
>   return $ TypeDecl p tc tvs' ty'
> checkDecl (TypeSig       p vs cx ty) =
>   TypeSig p vs cx `liftM` checkType ty
> checkDecl (FunctionDecl  p cty f eqs) =
>   FunctionDecl p cty f `liftM` mapM checkEquation eqs
> checkDecl (PatternDecl   p cty t rhs) =
>   PatternDecl p cty t `liftM` checkRhs rhs
> checkDecl (ForeignDecl p cc ie f ty) =
>   ForeignDecl p cc ie f `liftM` checkType ty
> checkDecl (ClassDecl p scon cls id0 decls) = 
>   ClassDecl p scon cls id0 `liftM` mapM checkDecl decls
> checkDecl (InstanceDecl p scon cls ty ids decls) = 
>   InstanceDecl p scon cls ty ids `liftM` mapM checkDecl decls
> checkDecl d                          = return d

> checkConstrDecl :: [Ident] -> ConstrDecl -> KCM ConstrDecl
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

> checkNewConstrDecl :: [Ident] -> NewConstrDecl -> KCM NewConstrDecl
> checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
>   evs' <- checkTypeLhs evs
>   ty'  <- checkClosedType (evs' ++ tvs) ty
>   return $ NewConstrDecl p evs' c ty'

> -- |Check the left-hand-side of a type declaration for
> -- * Anonymous type variables are allowed
> -- * only type variables (no type constructors)
> -- * linearity
> checkTypeLhs :: [Ident] -> KCM [Ident]
> checkTypeLhs []         = return []
> checkTypeLhs (tv : tvs) = do
>   unless (isAnonId tv) $ do
>     isTyCons <- (not . null . lookupKind tv) `liftM` getKindEnv
>     when isTyCons        $ report $ errNoVariable tv
>     when (tv `elem` tvs) $ report $ errNonLinear  tv
>   (tv :) `liftM` checkTypeLhs tvs

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: Equation -> KCM Equation
> checkEquation (Equation p lhs rhs) = Equation p lhs `liftM` checkRhs rhs

> checkRhs :: Rhs -> KCM Rhs
> checkRhs (SimpleRhs p e ds) =
>   liftM2 (SimpleRhs p) (checkExpr e) (mapM checkDecl ds)
> checkRhs (GuardedRhs es ds) =
>   liftM2 GuardedRhs (mapM checkCondExpr es) (mapM checkDecl ds)

> checkCondExpr :: CondExpr -> KCM CondExpr
> checkCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (checkExpr g) (checkExpr e)

> checkExpr :: Expression -> KCM Expression
> checkExpr l@(Literal         _) = return l
> checkExpr v@(Variable      _ _) = return v
> checkExpr c@(Constructor     _) = return c
> checkExpr (Paren             e) = Paren `liftM` checkExpr e
> checkExpr (Typed       e cx ty) = liftM3 Typed (checkExpr e) (return cx) (checkType ty)
> checkExpr (Tuple          p es) = Tuple p `liftM` mapM checkExpr es
> checkExpr (List           p es) = List  p `liftM` mapM checkExpr es
> checkExpr (ListCompr    p e qs) =
>   liftM2 (ListCompr p) (checkExpr e) (mapM checkStmt qs)
> checkExpr (EnumFrom         e) = EnumFrom `liftM` checkExpr e
> checkExpr (EnumFromThen  e1 e2) =
>   liftM2 EnumFromThen (checkExpr e1) (checkExpr e2)
> checkExpr (EnumFromTo    e1 e2) =
>   liftM2 EnumFromTo (checkExpr e1) (checkExpr e2)
> checkExpr (EnumFromThenTo e1 e2 e3) =
>   liftM3 EnumFromThenTo (checkExpr e1) (checkExpr e2) (checkExpr e3)
> checkExpr (UnaryMinus     op e) = UnaryMinus op `liftM` checkExpr e
> checkExpr (Apply       _ e1 e2) = liftM2 (Apply Nothing) (checkExpr e1) (checkExpr e2)
> checkExpr (InfixApply e1 op e2) =
>   liftM2 (\f1 f2 -> InfixApply f1 op f2) (checkExpr e1) (checkExpr e2)
> checkExpr (LeftSection    e op) = flip LeftSection op `liftM` checkExpr e
> checkExpr (RightSection   op e) = RightSection op `liftM` checkExpr e
> checkExpr (Lambda       r ts e) = Lambda r ts `liftM` checkExpr e
> checkExpr (Let            ds e) =
>   liftM2 Let (mapM checkDecl ds) (checkExpr e)
> checkExpr (Do            sts e) =
>   liftM2 Do (mapM checkStmt sts) (checkExpr e)
> checkExpr (IfThenElse r e1 e2 e3) =
>   liftM3 (IfThenElse r) (checkExpr e1) (checkExpr e2) (checkExpr e3)
> checkExpr (Case    r ct e alts) =
>   liftM2 (Case r ct) (checkExpr e) (mapM checkAlt alts)
> checkExpr (RecordConstr     fs) =
>   RecordConstr `liftM` mapM checkFieldExpr fs
> checkExpr (RecordSelection e l) =
>   flip RecordSelection l `liftM` checkExpr e
> checkExpr (RecordUpdate   fs e) =
>   liftM2 RecordUpdate (mapM checkFieldExpr fs) (checkExpr e)

> checkStmt :: Statement -> KCM Statement
> checkStmt (StmtExpr   p e) = StmtExpr p   `liftM` checkExpr e
> checkStmt (StmtBind p t e) = StmtBind p t `liftM` checkExpr e
> checkStmt (StmtDecl    ds) = StmtDecl     `liftM` mapM checkDecl ds

> checkAlt :: Alt -> KCM Alt
> checkAlt (Alt p t rhs) = Alt p t `liftM` checkRhs rhs

> checkFieldExpr :: Field Expression -> KCM (Field Expression)
> checkFieldExpr (Field p l e) = Field p l `liftM` checkExpr e

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: [Ident] -> TypeExpr -> KCM TypeExpr
> checkClosedType tvs ty = checkType ty >>= checkClosed tvs

> checkType :: TypeExpr -> KCM TypeExpr
> checkType c@(ConstructorType tc tys) = do
>   m <- getModuleIdent
>   kEnv <- getKindEnv
>   case qualLookupKind tc kEnv of
>     []
>       | not (isQualified tc) && null tys ->
>           return $ VariableType $ unqualify tc
>       | otherwise -> report (errUndefinedType tc) >> return c
>     [n]
>       | n == n'   -> ConstructorType tc `liftM` mapM checkType tys
>       | otherwise -> report (errWrongArity tc n n') >> return c
>     _ -> case qualLookupKind (qualQualify m tc) kEnv of
>       [n]
>         | n == n'   -> ConstructorType tc `liftM` mapM checkType tys
>         | otherwise -> report (errWrongArity tc n n') >> return c
>       _ -> report (errAmbiguousType tc) >> return c
>  where n' = length tys
> checkType (SpecialConstructorType (QualTC tc) tys) 
>   = checkType (ConstructorType tc tys)
> checkType v@(VariableType tv)
>   | isAnonId tv = return v
>   | otherwise   = checkType $ ConstructorType (qualify tv) []
> checkType (TupleType     tys) = TupleType `liftM` mapM checkType tys
> checkType (SpecialConstructorType UnitTC tys) 
>   = SpecialConstructorType UnitTC `liftM` mapM checkType tys
> checkType (SpecialConstructorType (TupleTC n) tys) 
>   = SpecialConstructorType (TupleTC n) `liftM` mapM checkType tys
> checkType (ListType       ty) = ListType  `liftM` checkType ty
> checkType (SpecialConstructorType ListTC tys) 
>   = SpecialConstructorType ListTC `liftM` mapM checkType tys
> checkType (ArrowType ty1 ty2) =
>   liftM2 ArrowType (checkType ty1) (checkType ty2)
> checkType (SpecialConstructorType ArrowTC tys) 
>   = SpecialConstructorType ArrowTC `liftM` mapM checkType tys
> checkType (RecordType   fs r) = do
>   fs' <- forM fs $ \ (l, ty) -> do
>     ty' <- checkType ty
>     return (l, ty')
>   r'  <- case r of
>     Nothing -> return Nothing
>     Just ar -> Just `liftM` checkType ar
>   return $ RecordType fs' r'

> checkClosed :: [Ident] -> TypeExpr -> KCM TypeExpr
> checkClosed tvs (ConstructorType tc tys) =
>   ConstructorType tc `liftM` mapM (checkClosed tvs) tys
> checkClosed tvs (SpecialConstructorType (QualTC tc) tys) = 
>   checkClosed tvs (ConstructorType tc tys)
> checkClosed tvs v@(VariableType      tv) = do
>   when (isAnonId tv || tv `notElem` tvs) $ report $ errUnboundVariable tv
>   return v
> checkClosed tvs (TupleType     tys) =
>   TupleType `liftM` mapM (checkClosed tvs) tys
> checkClosed tvs (SpecialConstructorType UnitTC tys) = 
>   SpecialConstructorType UnitTC `liftM` mapM (checkClosed tvs) tys
> checkClosed tvs (SpecialConstructorType (TupleTC n) tys) = 
>   SpecialConstructorType (TupleTC n) `liftM` mapM (checkClosed tvs) tys
> checkClosed tvs (ListType       ty) =
>   ListType `liftM` checkClosed tvs ty
> checkClosed tvs (SpecialConstructorType ListTC tys) = 
>   SpecialConstructorType ListTC `liftM` mapM (checkClosed tvs) tys
> checkClosed tvs (ArrowType ty1 ty2) =
>   liftM2 ArrowType (checkClosed tvs ty1) (checkClosed tvs ty2)
> checkClosed tvs (SpecialConstructorType ArrowTC tys) = 
>   SpecialConstructorType ArrowTC `liftM` mapM (checkClosed tvs) tys
> checkClosed tvs (RecordType   fs r) = do
>   fs' <- forM fs $ \ (l, ty) -> do
>     ty' <- checkClosed tvs ty
>     return (l, ty')
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

> errUndefinedType :: QualIdent -> Message
> errUndefinedType tc = posMessage tc $ hsep $ map text
>   ["Undefined type", qualName tc]

> errAmbiguousType :: QualIdent -> Message
> errAmbiguousType tc = posMessage tc $ hsep $ map text
>   ["Ambiguous type", qualName tc]

> errMultipleDeclaration :: [Ident] -> Message
> errMultipleDeclaration []     = internalError
>   "KindCheck.errMultipleDeclaration: empty list"
> errMultipleDeclaration (i:is) = posMessage i $
>   text "Multiple declarations for type" <+> text (escName i)
>   <+> text "at:" $+$
>   nest 2 (vcat (map showPos (i:is)))
>   where showPos = text . showLine . idPosition

> errNonLinear :: Ident -> Message
> errNonLinear tv = posMessage tv $ hsep $ map text
>   [ "Type variable", idName tv
>   , "occurs more than once on left hand side of type declaration"]

> errNoVariable :: Ident -> Message
> errNoVariable tv = posMessage tv $ hsep $ map text
>   [ "Type constructor", idName tv
>   , "used in left hand side of type declaration"]

> errWrongArity :: QualIdent -> Int -> Int -> Message
> errWrongArity tc arity argc = posMessage tc $
>   text "Type constructor" <+> text (qualName tc)
>   <+> text "expects" <+> text (arguments arity)
>   <> comma <+> text "but is applied to" <+> text (show argc)
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> errUnboundVariable :: Ident -> Message
> errUnboundVariable tv = posMessage tv $ hsep $ map text
>   ["Unbound type variable", idName tv]

\end{verbatim}
