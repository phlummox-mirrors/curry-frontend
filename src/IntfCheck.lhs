% -*- LaTeX -*-
% $Id: IntfCheck.lhs,v 1.23 2004/02/29 11:31:43 wlux Exp $
%
% Copyright (c) 2000-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfCheck.lhs}
\section{Checking Interface Files}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler checks that the definitions of the imported
entities are compatible with their original definitions and that all
type constructor applications are saturated.
\begin{verbatim}

> module IntfCheck(intfCheck,fixInterface,intfEquiv) where
> import Base
> import Maybe
> import List(deleteFirstsBy)
> import Set

\end{verbatim}
The function \texttt{intfCheck} is the main entry-point into this 
module.
\begin{verbatim}

> intfCheck :: PEnv -> TCEnv -> ValueEnv -> Interface -> Interface
> intfCheck pEnv tcEnv tyEnv (Interface m ds) =
>   Interface m (map (checkImport pEnv tcEnv tyEnv . checkIDecl tcEnv') ds)
>   where tcEnv' = foldr (bindArity m) tcEnv ds

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in the interface.
\begin{verbatim}

> bindArity :: ModuleIdent -> IDecl -> TCEnv -> TCEnv
> bindArity m (HidingDataDecl _ tc tvs) = bindTypeInfo DataType m tc tvs []
> bindArity m (IDataDecl _ tc tvs _) = bindLocalInfo DataType m tc tvs []
> bindArity m (INewtypeDecl _ tc tvs _) =
>   bindLocalInfo RenamingType m tc tvs undefined
> bindArity m (ITypeDecl _ tc tvs ty) =
>   bindLocalInfo AliasType m tc tvs undefined
> bindArity _ _ = id

> bindLocalInfo :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent
>               -> QualIdent -> [Ident] -> a -> TCEnv -> TCEnv
> bindLocalInfo f m tc tvs x
>   | isJust m' = id
>   | otherwise = bindTypeInfo f m tc' tvs x
>   where (m',tc') = splitQualIdent tc

\end{verbatim}
The checks applied to the interface are similar to those in the
kind-checker. However, there are no nested declarations. In addition,
synonym types must not occur in type expressions.
\begin{verbatim}

> checkIDecl :: TCEnv -> IDecl -> IDecl
> checkIDecl tcEnv (HidingDataDecl p tc tvs) =
>   HidingDataDecl p tc (checkTypeLhs tcEnv p tvs)
> checkIDecl tcEnv (IDataDecl p tc tvs cs) =
>   IDataDecl p tc tvs' (map (fmap (checkConstrDecl tcEnv tvs')) cs)
>   where tvs' = checkTypeLhs tcEnv p tvs
> checkIDecl tcEnv (INewtypeDecl p tc tvs nc) =
>   INewtypeDecl p tc tvs' (checkNewConstrDecl tcEnv tvs' nc)
>   where tvs' = checkTypeLhs tcEnv p tvs
> checkIDecl tcEnv (ITypeDecl p tc tvs ty) =
>   ITypeDecl p tc tvs' (checkClosedType tcEnv p tvs' ty)
>   where tvs' = checkTypeLhs tcEnv p tvs
> checkIDecl tcEnv (IFunctionDecl p f ty) =
>   IFunctionDecl p f (checkType tcEnv p ty)
> checkIDecl tcEnv decl = decl

> checkTypeLhs :: TCEnv -> Position -> [Ident] -> [Ident]
> checkTypeLhs tcEnv p (tv:tvs)
>   | isTypeConstr tv = errorAt p (noVariable tv)
>   | tv `elem` tvs = errorAt p  (nonLinear tv)
>   | otherwise = tv : checkTypeLhs tcEnv p tvs
>   where isTypeConstr tv = not (null (lookupTC tv tcEnv))
> checkTypeLhs tcEnv p [] = []

> checkConstrDecl :: TCEnv -> [Ident] -> ConstrDecl -> ConstrDecl
> checkConstrDecl tcEnv tvs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs' c (map (checkClosedType tcEnv p tvs') tys)
>   where evs' = checkTypeLhs tcEnv p evs
>         tvs' = evs' ++ tvs
> checkConstrDecl tcEnv tvs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs' (checkClosedType tcEnv p tvs' ty1) op
>             (checkClosedType tcEnv p tvs' ty2)
>   where evs' = checkTypeLhs tcEnv p evs
>         tvs' = evs' ++ tvs

> checkNewConstrDecl :: TCEnv -> [Ident] -> NewConstrDecl -> NewConstrDecl
> checkNewConstrDecl tcEnv tvs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs' c (checkClosedType tcEnv p tvs' ty)
>   where evs' = checkTypeLhs tcEnv p evs
>         tvs' = evs' ++ tvs

> checkClosedType :: TCEnv -> Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosedType tcEnv p tvs ty = checkClosed p tvs (checkType tcEnv p ty)

> checkType :: TCEnv -> Position -> TypeExpr -> TypeExpr
> checkType tcEnv p (ConstructorType tc tys) =
>   case qualLookupTC tc tcEnv of
>     []
>       | not (isQualified tc) && null tys -> VariableType (unqualify tc)
>       | otherwise -> errorAt p (undefinedType tc)
>     [DataType tc n _] -> constrType tc n
>     [RenamingType tc n _] -> constrType tc n
>     [AliasType tc n ty] -> errorAt p (badTypeSynonym tc)
>     _ -> internalError "checkType"
>   where constrType tc n
>           | n == n' = ConstructorType tc (map (checkType tcEnv p) tys)
>           | otherwise = errorAt p (wrongArity tc n n')
>           where n' = length tys
> checkType tcEnv p (VariableType tv) =
>   checkType tcEnv p (ConstructorType (qualify tv) [])
> checkType tcEnv p (TupleType tys) = TupleType (map (checkType tcEnv p) tys)
> checkType tcEnv p (ListType ty) = ListType (checkType tcEnv p ty)
> checkType tcEnv p (ArrowType ty1 ty2) =
>   ArrowType (checkType tcEnv p ty1) (checkType tcEnv p ty2)

> checkClosed :: Position -> [Ident] -> TypeExpr -> TypeExpr
> checkClosed p tvs (ConstructorType tc tys) =
>   ConstructorType tc (map (checkClosed p tvs) tys)
> checkClosed p tvs (VariableType tv)
>   | tv `notElem` tvs = errorAt p (unboundVariable tv)
>   | otherwise = VariableType tv
> checkClosed p tvs (TupleType tys) =
>   TupleType (map (checkClosed p tvs) tys)
> checkClosed p tvs (ListType ty) =
>   ListType (checkClosed p tvs ty)
> checkClosed p tvs (ArrowType ty1 ty2) =
>   ArrowType (checkClosed p tvs ty1) (checkClosed p tvs ty2)

\end{verbatim}
After checking the declarations, the compiler also asserts that all
imported definitions actually match their original definition.
\begin{verbatim}

> checkImport :: PEnv -> TCEnv -> ValueEnv -> IDecl -> IDecl
> checkImport _ _ _ (IImportDecl p m) = IImportDecl p m
> checkImport pEnv _ _ (IInfixDecl p fix pr op) =
>   case splitQualIdent op of
>     (Just m,op') ->
>       case qualLookupP op pEnv of
>         [] -> errorAt p (noPrecedence m op')
>         [PrecInfo op'' (OpPrec fix' pr')]
>           | op == op'' && fix == fix' && pr == pr' -> IInfixDecl p fix pr op
>           | otherwise -> errorAt p (importConflict "precedence" m op')
>         _ -> internalError "checkImport (IInfixDecl)"
>     (Nothing,_) -> IInfixDecl p fix pr op
> checkImport _ _ _ (HidingDataDecl p tc tvs) = HidingDataDecl p tc tvs
> checkImport _ tcEnv tyEnv (IDataDecl p tc tvs cs) =
>   case splitQualIdent tc of
>     (Just m,tc') ->
>       case qualLookupTC tc tcEnv of
>         [] -> errorAt p (notExported "data type" m tc')
>         [DataType tc'' n cs']
>           | tc == tc'' && length tvs == n && length cs <= length cs' ->
>               IDataDecl p tc tvs
>                 (zipWith (fmap . checkConstrImport m tc' tvs tyEnv) cs' cs)
>         [RenamingType tc'' n _]
>           | tc == tc'' && length tvs == n && null cs -> IDataDecl p tc tvs []
>         [_] -> errorAt p (importConflict "data type" m tc')
>         _ -> internalError "checkImport (IDataDecl)"
>     (Nothing,_) -> IDataDecl p tc tvs cs
> checkImport _ tcEnv tyEnv (INewtypeDecl p tc tvs nc) =
>   case splitQualIdent tc of
>     (Just m,tc') ->
>       case qualLookupTC tc tcEnv of
>         [] -> errorAt p (notExported "newtype" m tc')
>         [RenamingType tc'' n nc']
>           | tc == tc'' && length tvs == n ->
>               INewtypeDecl p tc tvs
>                 (checkNewConstrImport m tc' tvs tyEnv nc' nc)
>         [_] -> errorAt p (importConflict "newtype" m tc')
>         _ -> internalError "checkImport (INewtypeDecl)"
>     (Nothing,_) -> INewtypeDecl p tc tvs nc
> checkImport _ tcEnv _ (ITypeDecl p tc tvs ty) =
>   case splitQualIdent tc of
>     (Just m,tc') -> 
>       case qualLookupTC tc tcEnv of
>         [] -> errorAt p (notExported "synonym type" m tc')
>         [AliasType tc'' n ty']
>           | tc == tc'' && length tvs == n && toQualType m tvs ty == ty' ->
>               ITypeDecl p tc tvs ty
>         [_] -> errorAt p (importConflict "synonym type" m tc')
>         _ -> internalError "checkImport (ITypeDecl)"
>     (Nothing,_) -> ITypeDecl p tc tvs ty
> checkImport _ _ tyEnv (IFunctionDecl p f ty) =
>   case splitQualIdent f of
>     (Just m,f') ->
>       case qualLookupValue f tyEnv of
>         [] -> errorAt p (notExported "function" m f')
>         [Value f'' (ForAll _ ty')]
>           | f == f'' && toQualType m [] ty == ty' -> IFunctionDecl p f ty
>         [_] -> errorAt p (importConflict "function" m f')
>         _ -> internalError "checkImport (IFunctionDecl)"
>     (Nothing,_) -> IFunctionDecl p f ty

> checkConstrImport :: ModuleIdent -> Ident -> [Ident] -> ValueEnv
>                   -> Maybe (Data [Type]) -> ConstrDecl -> ConstrDecl
> checkConstrImport m tc tvs tyEnv (Just (Data c n tys))
>                                  (ConstrDecl p evs c' tys')
>   | c == c' && n == length evs && tys == toQualTypes m tvs tys' =
>       case qualLookupValue qc tyEnv of
>         [] -> errorAt p (notExported "data constructor" m c)
>         [DataConstructor c'' _]
>           | qc == c'' -> ConstrDecl p evs c' tys'
>         [_] -> errorAt p (importConflict "data constructor" m c)
>         _ -> internalError "checkConstrImport"
>   | otherwise = errorAt p (importConflict "data type" m tc)
>   where qc = qualifyWith m c
> checkConstrImport m tc tvs tyEnv (Just (Data c n tys))
>                                  (ConOpDecl p evs ty1 op ty2)
>   | c == op && n == length evs && tys == toQualTypes m tvs [ty1,ty2] =
>       case qualLookupValue qc tyEnv of
>         [] -> errorAt p (notExported "data constructor" m c)
>         [DataConstructor c' _]
>           | qc == c' -> ConOpDecl p evs ty1 op ty2
>         [_] -> errorAt p (importConflict "data constructor" m c)
>         _ -> internalError "checkConstrImport"
>   | otherwise = errorAt p (importConflict "data type" m tc)
>   where qc = qualifyWith m c
> checkConstrImport m tc _ _ Nothing d =
>   errorAt (pos d) (importConflict "data type" m tc)
>   where pos (ConstrDecl p _ _ _) = p
>         pos (ConOpDecl p _ _ _ _) = p

> checkNewConstrImport :: ModuleIdent -> Ident -> [Ident] -> ValueEnv
>                      -> Data Type -> NewConstrDecl -> NewConstrDecl
> checkNewConstrImport m tc tvs tyEnv (Data c n ty)
>                                     (NewConstrDecl p evs c' ty')
>   | c == c' && n == length evs && ty == toQualType m tvs ty' =
>       case qualLookupValue qc tyEnv of
>         [] -> errorAt p (notExported "newtype constructor" m c)
>         [NewtypeConstructor c'' _]
>           | qc == c'' -> NewConstrDecl p evs c' ty'
>         [_] -> errorAt p (importConflict "newtype constructor" m c)
>         _ -> internalError "checkNewConstrImport"
>   | otherwise = errorAt p (importConflict "newtype" m tc)
>   where qc = qualifyWith m c

\end{verbatim}
If a module is recompiled, the compiler has to check whether the
interface file must be updated. This must be done if any exported
entity has been changed, or an export was removed or added. The
function \texttt{intfEquiv} checks whether two interfaces are
equivalent, i.e., whether they define the same entities. The order
of declarations is ignored.

If we check for a change in the interface we do not need to check the
interface declarations, but must still disambiguate (nullary) type
constructors and type variables in type expressions. This is handled
by the function \texttt{fixInterface}.

\textbf{Note:} When comparing two data type declarations we must check
that the number of constructor declarations is the same in both
declarations.  Recall that the export code will remove the
declarations for the right most data constructors if they are hidden.
Using \texttt{zipWith iconstrEquiv} is not sufficient as it succeeds
for list of different lengths if they are equal up to the length of
the shorter list.
\begin{verbatim}

> intfEquiv :: Interface -> Interface -> Bool
> Interface m1 ds1 `intfEquiv` Interface m2 ds2 =
>   m1 == m2 && not (disjointBy declEquiv ds1 ds2)

> declEquiv :: IDecl -> IDecl -> Bool
> declEquiv (IImportDecl _ m1) (IImportDecl _ m2) = m1 == m2
> declEquiv (IInfixDecl _ fix1 p1 op1) (IInfixDecl _ fix2 p2 op2) =
>   fix1 == fix2 && p1 == p2 && op1 == op2
> declEquiv (HidingDataDecl _ tc1 tvs1) (HidingDataDecl _ tc2 tvs2) =
>   tc1 == tc2 && tvs1 == tvs2
> declEquiv (IDataDecl _ tc1 tvs1 cs1) (IDataDecl _ tc2 tvs2 cs2) =
>   tc1 == tc2 && tvs1 == tvs2 && length cs1 == length cs2 &&
>   and (zipWith iconstrEquiv cs1 cs2)
>   where iconstrEquiv = maybe isNothing (maybe False . constrEquiv)
> declEquiv (INewtypeDecl _ tc1 tvs1 nc1) (INewtypeDecl _ tc2 tvs2 nc2) =
>   tc1 == tc2 && tvs1 == tvs2 && newConstrEquiv nc1 nc2
> declEquiv (ITypeDecl _ tc1 tvs1 ty1) (ITypeDecl _ tc2 tvs2 ty2) = 
>   tc1 == tc2 && tvs1 == tvs2 && ty1 == ty2
> declEquiv (IFunctionDecl _ f1 ty1) (IFunctionDecl _ f2 ty2) =
>   f1 == f2 && ty1 == ty2
> declEquiv _ _ = False

> constrEquiv :: ConstrDecl -> ConstrDecl -> Bool
> constrEquiv (ConstrDecl _ evs1 c1 tys1) (ConstrDecl _ evs2 c2 tys2) =
>   c1 == c2 && evs1 == evs2 && tys1 == tys2
> constrEquiv (ConOpDecl _ evs1 ty11 op1 ty12)
>             (ConOpDecl _ evs2 ty21 op2 ty22) =
>   op1 == op2 && evs1 == evs2 && ty11 == ty21 && ty12 == ty22
> constrEquiv _ _ = False

> newConstrEquiv :: NewConstrDecl -> NewConstrDecl -> Bool
> newConstrEquiv (NewConstrDecl _ evs1 c1 ty1) (NewConstrDecl _ evs2 c2 ty2) =
>   c1 == c2 && evs1 == evs2 && ty1 == ty2

> disjointBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
> disjointBy eq xs ys =
>   not (null (deleteFirstsBy eq xs ys ++ deleteFirstsBy eq ys xs))

> fixInterface :: Interface -> Interface
> fixInterface (Interface m ds) =
>   Interface m (map (fixIDecl (fromListSet (typeConstructors ds))) ds)

> fixIDecl :: Set Ident -> IDecl -> IDecl
> fixIDecl tcs (IDataDecl p tc tvs cs) =
>   IDataDecl p tc tvs (map (fmap (fixConstrDecl tcs)) cs)
> fixIDecl tcs (INewtypeDecl p tc tvs nc) =
>   INewtypeDecl p tc tvs (fixNewConstrDecl tcs nc)
> fixIDecl tcs (ITypeDecl p tc tvs ty) = ITypeDecl p tc tvs (fixType tcs ty)
> fixIDecl tcs (IFunctionDecl p f ty) = IFunctionDecl p f (fixType tcs ty)
> fixIDecl tcs decl = decl

> fixConstrDecl :: Set Ident -> ConstrDecl -> ConstrDecl
> fixConstrDecl tcs (ConstrDecl p evs c tys) =
>   ConstrDecl p evs c (map (fixType tcs) tys)
> fixConstrDecl tcs (ConOpDecl p evs ty1 op ty2) =
>   ConOpDecl p evs (fixType tcs ty1) op (fixType tcs ty2)

> fixNewConstrDecl :: Set Ident -> NewConstrDecl -> NewConstrDecl
> fixNewConstrDecl tcs (NewConstrDecl p evs c ty) =
>   NewConstrDecl p evs c (fixType tcs ty)

> fixType :: Set Ident -> TypeExpr -> TypeExpr
> fixType tcs (ConstructorType tc [])
>   | not (isQualified tc) && tc' `notElemSet` tcs = VariableType tc'
>   where tc' = unqualify tc
> fixType tcs (ConstructorType tc tys) =
>   ConstructorType tc (map (fixType tcs) tys)
> fixType tcs (VariableType tv)
>   | tv `elemSet` tcs = ConstructorType (qualify tv) []
>   | otherwise = VariableType tv
> fixType tcs (TupleType tys) = TupleType (map (fixType tcs) tys)
> fixType tcs (ListType ty) = ListType (fixType tcs ty)
> fixType tcs (ArrowType ty ty') = ArrowType (fixType tcs ty) (fixType tcs ty')

> typeConstructors :: [IDecl] -> [Ident]
> typeConstructors = foldr tcs []
>   where tcs (HidingDataDecl _ tc _) tcs = tc : tcs
>         tcs (IDataDecl _ tc _ _) tcs = localTC tc tcs
>         tcs (INewtypeDecl _ tc _ _) tcs = localTC tc tcs
>         tcs (ITypeDecl _ tc _ _) tcs = localTC tc tcs
>         tcs _ tcs = tcs
>         localTC tc = maybe (tc' :) (const id) m'
>           where (m',tc') = splitQualIdent tc

\end{verbatim}
Error functions:
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type constructor " ++ qualName tc

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

> badTypeSynonym :: QualIdent -> String
> badTypeSynonym tc = "Synonym type " ++ qualName tc ++ " in interface"

> notExported :: String -> ModuleIdent -> Ident -> String
> notExported what m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not export " ++ what ++ " " ++ name x

> noPrecedence :: ModuleIdent -> Ident -> String
> noPrecedence m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not define a precedence for " ++ name x

> importConflict :: String -> ModuleIdent -> Ident -> String
> importConflict what m x =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of " ++ what ++ " " ++ name x ++
>   " does not match its definition in module " ++ moduleName m

\end{verbatim}
