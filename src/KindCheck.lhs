
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

> module KindCheck(kindCheck,kindCheckGoal) where
> import Base hiding (bindArity)
> import Maybe
> import TopEnv

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment containing the kind information for all type
constructors. The function \texttt{kindCheck} first initializes this
environment by filtering out the arity of each type constructor from
the imported type environment. Next, the arities of all locally
defined type constructors are inserted into the environment, and,
finally, the declarations are checked within this environment.
\begin{verbatim}

> kindCheck :: ModuleIdent -> TCEnv -> [Decl] -> [Decl]
> kindCheck m tcEnv ds =
>   case linear (map tconstr ds') of
>     Linear -> map (checkDecl m kEnv) ds
>     NonLinear (PIdent p tc) -> errorAt p (duplicateType tc)
>   where ds' = filter isTypeDecl ds
>         kEnv = foldr (bindArity m) (fmap tcArity tcEnv) ds'

> kindCheckGoal :: TCEnv -> Goal -> Goal
> kindCheckGoal tcEnv (Goal p e ds) =
>   Goal p (checkExpr m kEnv p e) (map (checkDecl m kEnv) ds)
>   where kEnv = fmap tcArity tcEnv
>	  m = mkMIdent []

\end{verbatim}
The kind environment only needs to record the arity of each type constructor.
\begin{verbatim}

> type KindEnv = TopEnv Int

> bindArity :: ModuleIdent -> Decl -> KindEnv -> KindEnv
> bindArity m (DataDecl p tc tvs _) = bindArity' m p tc tvs
> bindArity m (NewtypeDecl p tc tvs _) = bindArity' m p tc tvs
> bindArity m (TypeDecl p tc tvs _) = bindArity' m p tc tvs
> bindArity _ _ = id

> bindArity' :: ModuleIdent -> Position -> Ident -> [Ident]
>            -> KindEnv -> KindEnv
> bindArity' m p tc tvs 
>   = bindTopEnv "KindCheck.bindArity'" tc n 
>                . qualBindTopEnv "KindCheck.bindArity'" (qualifyWith m tc) n
>   where n = length tvs

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

> checkDecl :: ModuleIdent -> KindEnv -> Decl -> Decl
> checkDecl m kEnv (DataDecl p tc tvs cs) =
>   DataDecl p tc tvs' (map (checkConstrDecl m kEnv tvs') cs)
>   where tvs' = checkTypeLhs kEnv p tvs
> checkDecl m kEnv (NewtypeDecl p tc tvs nc) =
>   NewtypeDecl p tc tvs' (checkNewConstrDecl m kEnv tvs' nc)
>   where tvs' = checkTypeLhs kEnv p tvs
> checkDecl m kEnv (TypeDecl p tc tvs ty) =
>   TypeDecl p tc tvs' (checkClosedType m kEnv p tvs' ty)
>   where tvs' = checkTypeLhs kEnv p tvs
> checkDecl m kEnv (TypeSig p vs ty) =
>   TypeSig p vs (checkType m kEnv p ty)
> checkDecl m kEnv (FunctionDecl p f eqs) =
>   FunctionDecl p f (map (checkEquation m kEnv) eqs)
> checkDecl m kEnv (PatternDecl p t rhs) =
>   PatternDecl p t (checkRhs m kEnv rhs)
> checkDecl m kEnv (ExternalDecl p cc ie f ty) =
>   ExternalDecl p cc ie f (checkType m kEnv p ty)
> checkDecl _ _ d = d

> checkTypeLhs :: KindEnv -> Position -> [Ident] -> [Ident]
> checkTypeLhs kEnv p (tv:tvs)
>   | tv == anonId = tv : checkTypeLhs kEnv p tvs
>   | isTypeConstr tv = errorAt p (noVariable tv)
>   | tv `elem` tvs = errorAt p (nonLinear tv)
>   | otherwise = tv : checkTypeLhs kEnv p tvs
>   where isTypeConstr tv = not (null (lookupKind tv kEnv))
> checkTypeLhs kEnv p [] = []

> checkConstrDecl :: ModuleIdent -> KindEnv -> [Ident] -> ConstrDecl -> ConstrDecl
> checkConstrDecl m kEnv tvs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs' c (map (checkClosedType m kEnv p tvs') tys)
>   where evs' = checkTypeLhs kEnv p evs
>         tvs' = evs' ++ tvs
> checkConstrDecl m kEnv tvs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs' (checkClosedType m kEnv p tvs' ty1) op
>             (checkClosedType m kEnv p tvs' ty2)
>   where evs' = checkTypeLhs kEnv p evs
>         tvs' = evs' ++ tvs

> checkNewConstrDecl :: ModuleIdent -> KindEnv -> [Ident] -> NewConstrDecl 
>	     -> NewConstrDecl
> checkNewConstrDecl m kEnv tvs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs' c (checkClosedType m kEnv p tvs' ty)
>   where evs' = checkTypeLhs kEnv p evs
>         tvs' = evs' ++ tvs

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: ModuleIdent -> KindEnv -> Equation -> Equation
> checkEquation m kEnv (Equation p lhs rhs) = 
>     Equation p lhs (checkRhs m kEnv rhs)

> checkRhs :: ModuleIdent -> KindEnv -> Rhs -> Rhs
> checkRhs m kEnv (SimpleRhs p e ds) =
>   SimpleRhs p (checkExpr m kEnv p e) (map (checkDecl m kEnv) ds)
> checkRhs m kEnv (GuardedRhs es ds) =
>   GuardedRhs (map (checkCondExpr m kEnv) es) (map (checkDecl m kEnv) ds)

> checkCondExpr :: ModuleIdent -> KindEnv -> CondExpr -> CondExpr
> checkCondExpr m kEnv (CondExpr p g e) =
>   CondExpr p (checkExpr m kEnv p g) (checkExpr m kEnv p e)

> checkExpr :: ModuleIdent -> KindEnv -> Position -> Expression -> Expression
> checkExpr _ _ _ (Literal l) = Literal l
> checkExpr _ _ _ (Variable v) = Variable v
> checkExpr _ _ _ (Constructor c) = Constructor c
> checkExpr m kEnv p (Paren e) = Paren (checkExpr m kEnv p e)
> checkExpr m kEnv p (Typed e ty) =
>   Typed (checkExpr m kEnv p e) (checkType m kEnv p ty)
> checkExpr m kEnv p (Tuple es) = Tuple (map (checkExpr m kEnv p) es)
> checkExpr m kEnv p (List es) = List (map (checkExpr m kEnv p) es)
> checkExpr m kEnv p (ListCompr e qs) =
>   ListCompr (checkExpr m kEnv p e) (map (checkStmt m kEnv p) qs)
> checkExpr m kEnv p (EnumFrom e) = EnumFrom (checkExpr m kEnv p e)
> checkExpr m kEnv p (EnumFromThen e1 e2) =
>   EnumFromThen (checkExpr m kEnv p e1) (checkExpr m kEnv p e2)
> checkExpr m kEnv p (EnumFromTo e1 e2) =
>   EnumFromTo (checkExpr m kEnv p e1) (checkExpr m kEnv p e2)
> checkExpr m kEnv p (EnumFromThenTo e1 e2 e3) =
>   EnumFromThenTo (checkExpr m kEnv p e1) (checkExpr m kEnv p e2)
>                  (checkExpr m kEnv p e3)
> checkExpr m kEnv p (UnaryMinus op e) = UnaryMinus op (checkExpr m kEnv p e)
> checkExpr m kEnv p (Apply e1 e2) =
>   Apply (checkExpr m kEnv p e1) (checkExpr m kEnv p e2)
> checkExpr m kEnv p (InfixApply e1 op e2) =
>   InfixApply (checkExpr m kEnv p e1) op (checkExpr m kEnv p e2)
> checkExpr m kEnv p (LeftSection e op) = LeftSection (checkExpr m kEnv p e) op
> checkExpr m kEnv p (RightSection op e) = RightSection op (checkExpr m kEnv p e)
> checkExpr m kEnv p (Lambda ts e) = Lambda ts (checkExpr m kEnv p e)
> checkExpr m kEnv p (Let ds e) =
>   Let (map (checkDecl m kEnv) ds) (checkExpr m kEnv p e)
> checkExpr m kEnv p (Do sts e) =
>   Do (map (checkStmt m kEnv p) sts) (checkExpr m kEnv p e)
> checkExpr m kEnv p (IfThenElse e1 e2 e3) =
>   IfThenElse (checkExpr m kEnv p e1) (checkExpr m kEnv p e2)
>              (checkExpr m kEnv p e3)
> checkExpr m kEnv p (Case e alts) =
>   Case (checkExpr m kEnv p e) (map (checkAlt m kEnv) alts)
> checkExpr m kEnv p (RecordConstr fs) =
>   RecordConstr (map (checkFieldExpr m kEnv) fs)
> checkExpr m kEnv p (RecordSelection e l) =
>   RecordSelection (checkExpr m kEnv p e) l
> checkExpr m kEnv p (RecordUpdate fs e) =
>   RecordUpdate (map (checkFieldExpr m kEnv) fs) (checkExpr m kEnv p e)

> checkStmt :: ModuleIdent -> KindEnv -> Position -> Statement -> Statement
> checkStmt m kEnv p (StmtExpr e) = StmtExpr (checkExpr m kEnv p e)
> checkStmt m kEnv p (StmtBind t e) = StmtBind t (checkExpr m kEnv p e)
> checkStmt m kEnv p (StmtDecl ds) = StmtDecl (map (checkDecl m kEnv) ds)

> checkAlt :: ModuleIdent -> KindEnv -> Alt -> Alt
> checkAlt m kEnv (Alt p t rhs) = Alt p t (checkRhs m kEnv rhs)

> checkFieldExpr :: ModuleIdent -> KindEnv -> Field Expression
>	            -> Field Expression
> checkFieldExpr m kEnv (Field p l e) = Field p l (checkExpr m kEnv p e)

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: ModuleIdent -> KindEnv -> Position -> [Ident] -> TypeExpr 
>	  -> TypeExpr
> checkClosedType m kEnv p tvs ty = checkClosed p tvs (checkType m kEnv p ty)

> checkType :: ModuleIdent -> KindEnv -> Position -> TypeExpr -> TypeExpr
> checkType m kEnv p (ConstructorType tc tys) =
>   case qualLookupKind tc kEnv of
>     []
>       | not (isQualified tc) && null tys -> VariableType (unqualify tc)
>       | otherwise -> errorAt p (undefinedType tc)
>     [n]
>       | n == n' -> ConstructorType tc (map (checkType m kEnv p) tys)
>       | otherwise -> errorAt p (wrongArity tc n n')
>     _ -> case (qualLookupKind (qualQualify m tc) kEnv) of
>            [n] 
>               | n == n' -> ConstructorType tc (map (checkType m kEnv p) tys)
>               | otherwise -> errorAt p (wrongArity tc n n')
>            _ -> errorAt p (ambiguousType tc)
>  where n' = length tys 
> checkType m kEnv p (VariableType tv)
>   | tv == anonId = VariableType tv
>   | otherwise = checkType m kEnv p (ConstructorType (qualify tv) [])
> checkType m kEnv p (TupleType tys) =
>   TupleType (map (checkType m kEnv p) tys)
> checkType m kEnv p (ListType ty) =
>   ListType (checkType m kEnv p ty)
> checkType m kEnv p (ArrowType ty1 ty2) =
>   ArrowType (checkType m kEnv p ty1) (checkType m kEnv p ty2)
> checkType m kEnv p (RecordType fs r) =
>   RecordType (map (\ (ls,ty) -> (ls, checkType m kEnv p ty)) fs)
>	       (maybe Nothing (Just . checkType m kEnv p) r)

> checkClosed :: Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosed p tvs (ConstructorType tc tys) =
>   ConstructorType tc (map (checkClosed p tvs) tys)
> checkClosed p tvs (VariableType tv)
>   | tv == anonId || tv `notElem` tvs = errorAt p (unboundVariable tv)
>   | otherwise = VariableType tv
> checkClosed p tvs (TupleType tys) =
>   TupleType (map (checkClosed p tvs) tys)
> checkClosed p tvs (ListType ty) =
>   ListType (checkClosed p tvs ty)
> checkClosed p tvs (ArrowType ty1 ty2) =
>   ArrowType (checkClosed p tvs ty1) (checkClosed p tvs ty2)
> checkClosed p tvs (RecordType fs r) =
>   RecordType (map (\ (ls,ty) -> (ls, checkClosed p tvs ty)) fs)
>	       (maybe Nothing (Just . checkClosed p tvs) r)
>       

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> tconstr :: Decl -> PIdent
> tconstr (DataDecl p tc _ _) = PIdent p tc
> tconstr (NewtypeDecl p tc _ _) = PIdent p tc
> tconstr (TypeDecl p tc _ _) = PIdent p tc
> tconstr _ = internalError "tconstr"

\end{verbatim}
Error messages:
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type " ++ qualName tc

> ambiguousType :: QualIdent -> String
> ambiguousType tc = "Ambiguous type " ++ qualName tc

> duplicateType :: Ident -> String
> duplicateType tc = "More than one definition for type " ++ name tc

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noVariable :: Ident -> String
> noVariable tv =
>   "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity tc arity argc =
>   "Type constructor " ++ qualName tc ++ " expects " ++ arguments arity ++
>   " but is applied to " ++ show argc
>   where arguments 0 = "no arguments"
>         arguments 1 = "1 argument"
>         arguments n = show n ++ " arguments"

> unboundVariable :: Ident -> String
> unboundVariable tv = "Unbound type variable " ++ name tv

\end{verbatim}
