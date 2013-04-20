% $Id: TypeCheck.lhs,v 1.90 2004/11/06 18:34:07 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% Modified by Björn Peemöller (bjp@informatik.uni-kiel.de)
%
\nwfilename{TypeCheck.lhs}
\section{Type Checking Curry Programs}
This module implements the type checker of the Curry compiler. The
type checker is invoked after the syntactic correctness of the program
has been verified. Local variables have been renamed already. Thus the
compiler can maintain a flat type environment (which is necessary in
order to pass the type information to later phases of the compiler).
The type checker now checks the correct typing of all expressions and
also verifies that the type signatures given by the user match the
inferred types. The type checker uses algorithm
W~\cite{DamasMilner82:Principal} for inferring the types of
unannotated declarations, but allows for polymorphic recursion when a
type annotation is present.
\begin{verbatim}

> module Checks.TypeCheck (typeCheck) where

> import Control.Monad (liftM, liftM2, liftM3, replicateM, unless)
> import qualified Control.Monad.State as S (State, execState, gets, modify)
> import Data.List (nub, partition)
> import qualified Data.Map as Map (Map, empty, insert, lookup)
> import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, listToMaybe, maybeToList)
> import qualified Data.Set as Set (Set, fromList, member, notMember, unions)
> import Text.PrettyPrint
> import Debug.Trace
> -- import Data.List (union)

> import Curry.Base.Ident
> import Curry.Base.Position
> import Curry.Syntax as ST
> import Curry.Syntax.Pretty

> import Base.CurryTypes (fromQualType, toConstrType, toConstrTypes)
> import Base.Expr
> import Base.Messages (Message, posMessage, internalError, message)
> import Base.SCC
> import Base.TopEnv
> import Base.Types as BT
> import Base.TypeSubst
> import Base.Subst (listToSubst)
> import Base.Utils (foldr2, concatMapM)

> import Env.TypeConstructor (TCEnv, TypeInfo (..), bindTypeInfo
>   , qualLookupTC)
> import Env.Value ( ValueEnv, ValueInfo (..), bindFun, rebindFun
>   , bindGlobalInfo, bindLabel, lookupValue, qualLookupValue )
> import Env.ClassEnv (ClassEnv, lookupMethodTypeScheme
>   , getAllClassMethods)

> infixl 5 $-$

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

\end{verbatim}
Type checking proceeds as follows. First, the type constructor
environment is initialized by adding all types defined in the current
module. Next, the types of all data constructors and field labels
are entered into the type environment and then a type inference
for all function and value definitions is performed.
The type checker returns the resulting type constructor and type environments.
\begin{verbatim}

> typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> [Decl]
>           -> (TCEnv, ValueEnv, [Message])
> typeCheck m tcEnv tyEnv cEnv decls = execTCM check initState
>   where
>   check = do
>     checkTypeSynonyms m tds
>     bindTypes tds
>     bindConstrs
>     bindLabels
>     bindClassMethods cEnv
>     _ <- tcDecls vds

>     cEnv' <- getClassEnv
>     vEnv <- getValueEnv
>     checkNoEqualClassMethodAndFunctionNames vEnv cEnv'
>   (tds, vds) = partition isTypeDecl decls
>   initState  = TcState m tcEnv tyEnv cEnv idSubst emptySigEnv 0 []

\end{verbatim}

The type checker makes use of a state monad in order to maintain the type
environment, the current substitution, and a counter which is used for
generating fresh type variables.
\begin{verbatim}

> data TcState = TcState
>   { moduleIdent :: ModuleIdent -- read only
>   , tyConsEnv   :: TCEnv
>   , valueEnv    :: ValueEnv
>   , classEnv    :: ClassEnv
>   , typeSubst   :: TypeSubst
>   , sigEnv      :: SigEnv
>   , nextId      :: Int         -- automatic counter
>   , errors      :: [Message]
>   }

> type TCM = S.State TcState

> getModuleIdent :: TCM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> getTyConsEnv :: TCM TCEnv
> getTyConsEnv = S.gets tyConsEnv

> setTyConsEnv :: TCEnv -> TCM ()
> setTyConsEnv tcEnv = S.modify $ \ s -> s { tyConsEnv = tcEnv }

> getValueEnv :: TCM ValueEnv
> getValueEnv = S.gets valueEnv

> getClassEnv :: TCM ClassEnv
> getClassEnv = S.gets classEnv

> modifyValueEnv :: (ValueEnv -> ValueEnv) -> TCM ()
> modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

> getTypeSubst :: TCM TypeSubst
> getTypeSubst = S.gets typeSubst

> modifyTypeSubst :: (TypeSubst -> TypeSubst) -> TCM ()
> modifyTypeSubst f = S.modify $ \ s -> s { typeSubst = f $ typeSubst s }

> getSigEnv :: TCM SigEnv
> getSigEnv = S.gets sigEnv

> modifySigEnv :: (SigEnv -> SigEnv) -> TCM ()
> modifySigEnv f = S.modify $ \ s -> s { sigEnv = f $ sigEnv s }

> getNextId :: TCM Int
> getNextId = do
>   nid <- S.gets nextId
>   S.modify $ \ s -> s { nextId = succ nid }
>   return nid

> report :: Message -> TCM ()
> report err = S.modify $ \ s -> s { errors = err : errors s }

> execTCM :: TCM a -> TcState -> (TCEnv, ValueEnv, [Message])
> execTCM tcm s = let s' = S.execState tcm s
>                 in  ( tyConsEnv s'
>                     , typeSubst s' `subst` valueEnv s'
>                     , reverse $ errors s'
>                     )

\end{verbatim}
\paragraph{Defining Types}
Before type checking starts, the types defined in the local module
have to be entered into the type constructor environment. All type
synonyms occurring in the definitions are fully expanded and all type
constructors are qualified with the name of the module in which they
are defined. This is possible because Curry does not allow (mutually)
recursive type synonyms. In order to simplify the expansion of type
synonyms, the compiler first performs a dependency analysis on the
type definitions. This also makes it easy to identify (mutually)
recursive synonyms.

Note that \texttt{bindTC} is passed the \emph{final} type constructor
environment in order to handle the expansion of type synonyms. This
does not lead to a termination problem because \texttt{sortTypeDecls}
already has checked that there are no recursive type synonyms.

We have to be careful with existentially quantified type variables for
data constructors. An existentially quantified type variable may
shadow a universally quantified variable from the left hand side of
the type declaration. In order to avoid wrong indices being assigned
to these variables, we replace all shadowed variables in the left hand
side by \texttt{anonId} before passing them to \texttt{expandMonoType}
and \texttt{expandMonoTypes}, respectively.
\begin{verbatim}

> checkTypeSynonyms :: ModuleIdent -> [Decl] -> TCM ()
> checkTypeSynonyms m = mapM_ (checkTypeDecls m) . scc bound free
>   where
>   bound (DataDecl    _ tc _ _) = [tc]
>   bound (NewtypeDecl _ tc _ _) = [tc]
>   bound (TypeDecl    _ tc _ _) = [tc]
>   bound _                      = []
>   free  (DataDecl     _ _ _ _) = []
>   free  (NewtypeDecl  _ _ _ _) = []
>   free  (TypeDecl    _ _ _ ty) = ft m ty []
>   free _                       = []

> checkTypeDecls :: ModuleIdent -> [Decl] -> TCM ()
> checkTypeDecls _ []                    =
>   internalError "TypeCheck.checkTypeDecls: empty list"
> checkTypeDecls _ [DataDecl    _ _ _ _] = return ()
> checkTypeDecls _ [NewtypeDecl _ _ _ _] = return ()
> checkTypeDecls m [TypeDecl  _ tc _ ty]
>   | tc `elem` ft m ty [] = report $ errRecursiveTypes [tc]
>   | otherwise            = return ()
> checkTypeDecls _ (TypeDecl _ tc _ _ : ds) =
>   report $ errRecursiveTypes $ tc : [tc' | TypeDecl _ tc' _ _ <- ds]
> checkTypeDecls _ _                     =
>   internalError "TypeCheck.checkTypeDecls: no type synonym"

> ft :: ModuleIdent -> TypeExpr -> [Ident] -> [Ident]
> ft m (ConstructorType tc tys) tcs =
>   maybe id (:) (localIdent m tc) (foldr (ft m) tcs tys)
> ft m (SpecialConstructorType (QualTC tc) tys) tcs = 
>   ft m (ConstructorType tc tys) tcs
> ft _ (VariableType         _) tcs = tcs
> ft m (TupleType          tys) tcs = foldr (ft m) tcs tys
> ft m (ListType            ty) tcs = ft m ty tcs
> ft m (ArrowType      ty1 ty2) tcs = ft m ty1 $ ft m ty2 $ tcs
> ft m (RecordType      fs rty) tcs =
>   foldr (ft m) (maybe tcs (\ty -> ft m ty tcs) rty) (map snd fs)
> ft m (SpecialConstructorType _ tys) tcs = 
>   foldr (ft m) tcs tys

> bindTypes :: [Decl] -> TCM ()
> bindTypes ds = do
>   m     <- getModuleIdent
>   tcEnv <- getTyConsEnv
>   let tcEnv' = foldr (bindTC m tcEnv') tcEnv ds
>   setTyConsEnv tcEnv'

> bindTC :: ModuleIdent -> TCEnv -> Decl -> TCEnv -> TCEnv
> bindTC m tcEnv (DataDecl _ {- cx -} tc tvs cs) =
>   bindTypeInfo DataType m tc tvs (map (Just . mkData) cs)
>   where
>   mkData (ConstrDecl _ evs     c  tys) = mkData' evs c  tys
>   mkData (ConOpDecl  _ evs ty1 op ty2) = mkData' evs op [ty1, ty2]
>   mkData' evs c tys = DataConstr c (length evs) $
>     -- TODO: somewhen adding contexts to data declarations
>     map getType $ expandMonoTypes m tcEnv (cleanTVars tvs evs) (map noBContext tys)
> bindTC m tcEnv (NewtypeDecl _ tc tvs (NewConstrDecl _ evs c ty)) =
>   bindTypeInfo RenamingType m tc tvs (DataConstr c (length evs) [ty'])
>   where ty' = getType $ expandMonoType' m tcEnv (cleanTVars tvs evs) (noBContext ty)
> bindTC m tcEnv (TypeDecl _ tc tvs ty) =
>   bindTypeInfo AliasType m tc tvs (getType $ expandMonoType' m tcEnv tvs (noBContext ty))
> bindTC _ _ _ = id

> cleanTVars :: [Ident] -> [Ident] -> [Ident]
> cleanTVars tvs evs = [if tv `elem` evs then anonId else tv | tv <- tvs]

> noBContext :: TypeExpr -> BaseConstrType
> noBContext texp = (ST.emptyContext, texp) 

\end{verbatim}
\paragraph{Defining Data Constructors}
In the next step, the types of all data constructors are entered into
the type environment using the information just entered into the type
constructor environment. Thus, we can be sure that all type variables
have been properly renamed and all type synonyms are already expanded.
\begin{verbatim}

> bindConstrs :: TCM ()
> bindConstrs = do
>   m <- getModuleIdent
>   tcEnv <- getTyConsEnv
>   modifyValueEnv $ bindConstrs' m tcEnv

> bindConstrs' :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
> bindConstrs' m tcEnv tyEnv = foldr (bindData . snd) tyEnv
>                            $ localBindings tcEnv
>   where
>   bindData (DataType tc n cs) tyEnv' =
>     foldr (bindConstr m n (constrType' tc n)) tyEnv' (catMaybes cs)
>   bindData (RenamingType tc n (DataConstr c n' [ty])) tyEnv' =
>     bindGlobalInfo NewtypeConstructor m c
>                    (ForAllExist BT.emptyContext n n' (TypeArrow ty (constrType' tc n)))
>                    tyEnv'
>   bindData (RenamingType _ _ (DataConstr _ _ _)) _ =
>     internalError "TypeCheck.bindConstrs: newtype with illegal constructors"
>   bindData (AliasType _ _ _) tyEnv' = tyEnv'
>   bindConstr m' n ty (DataConstr c n' tys) =
>     bindGlobalInfo (flip DataConstructor (length tys)) m' c
>                    (ForAllExist BT.emptyContext n n' (foldr TypeArrow ty tys))
>   constrType' tc n = TypeConstructor tc $ map TypeVariable [0 .. n - 1]

\end{verbatim}
\paragraph{Defining Field Labels}
Records can only be declared as type aliases. So currently there is
nothing more to do than entering all typed record fields (labels)
which occur in record types on the right-hand-side of type aliases
into the type environment. Since we use the type constructor environment
again, we can be sure that all type variables
have been properly renamed and all type synonyms are already expanded.
\begin{verbatim}

> bindLabels :: TCM ()
> bindLabels = do
>   tcEnv <- getTyConsEnv
>   modifyValueEnv $ bindLabels' tcEnv

> bindLabels' :: TCEnv -> ValueEnv -> ValueEnv
> bindLabels' tcEnv tyEnv = foldr (bindFieldLabels . snd) tyEnv
>                         $ localBindings tcEnv
>   where
>   bindFieldLabels (AliasType r _ (TypeRecord fs _)) env =
>     foldr (bindField r) env fs
>   bindFieldLabels _ env = env
>
>   bindField r (l, ty) env = case lookupValue l env of
>     [] -> bindLabel l r (polyType ty) env
>     _  -> env

\end{verbatim}
\paragraph{Type Signatures}
The type checker collects type signatures in a flat environment. All
anonymous variables occurring in a signature are replaced by fresh
names. However, the type is not expanded so that the signature is
available for use in the error message that is printed when the
inferred type is less general than the signature.
\begin{verbatim}

> type BaseConstrType = (ST.Context, TypeExpr)

> -- getSTType :: BaseConstrType -> TypeExpr
> -- getSTType (_cx, tyexp) = tyexp

> type SigEnv = Map.Map Ident BaseConstrType

> emptySigEnv :: SigEnv
> emptySigEnv = Map.empty

> bindTypeSig :: Ident -> BaseConstrType -> SigEnv -> SigEnv
> bindTypeSig = Map.insert

> bindTypeSigs :: Decl -> SigEnv -> SigEnv
> bindTypeSigs (TypeSig _ vs cx ty) env =
>   foldr (flip bindTypeSig (cx, nameSigType ty)) env vs
> bindTypeSigs _ env = env

> lookupTypeSig :: Ident -> SigEnv -> Maybe BaseConstrType
> lookupTypeSig = Map.lookup

> qualLookupTypeSig :: ModuleIdent -> QualIdent -> SigEnv 
>                   -> Maybe BaseConstrType
> qualLookupTypeSig m f sigs = localIdent m f >>= flip lookupTypeSig sigs

> nameSigType :: TypeExpr -> TypeExpr
> nameSigType ty = fst $ nameType ty $ filter (`notElem` fv ty) identSupply

> nameTypes :: [TypeExpr] -> [Ident] -> ([TypeExpr], [Ident])
> nameTypes []         tvs = ([]        , tvs  )
> nameTypes (ty : tys) tvs = (ty' : tys', tvs'')
>   where (ty' , tvs' ) = nameType ty tvs
>         (tys', tvs'') = nameTypes tys tvs'

> nameType :: TypeExpr -> [Ident] -> (TypeExpr, [Ident])
> nameType (ConstructorType tc tys) tvs = (ConstructorType tc tys', tvs')
>   where (tys', tvs') = nameTypes tys tvs
> nameType (SpecialConstructorType tc tys) tvs = (SpecialConstructorType tc tys', tvs')
>   where (tys', tvs') = nameTypes tys tvs
> nameType (VariableType tv) (tv' : tvs)
>   | isAnonId tv = (VariableType tv', tvs      )
>   | otherwise   = (VariableType tv , tv' : tvs)
> nameType (TupleType tys) tvs = (TupleType tys', tvs')
>   where (tys', tvs') = nameTypes tys tvs
> nameType (ListType ty) tvs = (ListType ty', tvs')
>   where (ty', tvs') = nameType ty tvs
> nameType (ArrowType ty1 ty2) tvs = (ArrowType ty1' ty2', tvs'')
>   where (ty1', tvs' ) = nameType ty1 tvs
>         (ty2', tvs'') = nameType ty2 tvs'
> nameType (RecordType fs rty) tvs =
>   (RecordType (zip ls tys') (listToMaybe rty'), tvs)
>   where (ls  , tys) = unzip fs
>         (tys', _  ) = nameTypes tys tvs
>         (rty', _  ) = nameTypes (maybeToList rty) tvs
> nameType (VariableType _) [] = internalError
>  "TypeCheck.nameType: empty ident list"

\end{verbatim}
All type signatures of defined class methods are loaded into the signature
environment as well. 
\begin{verbatim}

> bindClassMethods :: ClassEnv -> TCM ()
> bindClassMethods cEnv = 
>   let tySigs = getAllClassMethods cEnv
>   in modifySigEnv $ 
>      \sigs -> foldr (\(id0, cx, texp) sig -> bindTypeSig id0 (cx, texp) sig) 
>                     sigs tySigs

\end{verbatim}
\paragraph{Type Inference}
Before type checking a group of declarations, a dependency analysis is
performed and the declaration group is eventually transformed into
nested declaration groups which are checked separately. Within each
declaration group, first the left hand sides of all declarations are
typed. Next, the right hand sides of the declarations are typed in the
extended type environment. Finally, the types for the left and right
hand sides are unified and the types of all defined functions are
generalized. The generalization step will also check that the type
signatures given by the user match the inferred types.

Argument and result types of foreign functions using the
\texttt{ccall} calling convention are restricted to the basic types
\texttt{Bool}, \texttt{Char}, \texttt{Int}, and \texttt{Float}. In
addition, \texttt{IO}~$t$ is a legitimate result type when $t$ is
either one of the basic types or \texttt{()}.

\ToDo{Extend the set of legitimate types to match the types admitted
  by the Haskell Foreign Function Interface
  Addendum.~\cite{Chakravarty03:FFI}}
\begin{verbatim}

> tcDecls :: [Decl] -> TCM BT.Context
> tcDecls ds = do
>   m <- getModuleIdent
>   oldSig <- getSigEnv
>   modifySigEnv $ \ sigs -> foldr bindTypeSigs sigs ods
>   cxs <- mapM tcDeclGroup $ scc bv (qfv m) vds
>   modifySigEnv (const oldSig)
>   return $ concat cxs
>   where (vds, ods) = partition isValueDecl ds

> tcDeclGroup :: [Decl] -> TCM BT.Context
> tcDeclGroup [ForeignDecl _ _ _ f ty] = tcForeign f ty >> return BT.emptyContext
> tcDeclGroup [ExternalDecl      _ fs] = mapM_ tcExternal fs >> return BT.emptyContext
> tcDeclGroup [FreeDecl          _ vs] = mapM_ tcFree     vs >> return BT.emptyContext
> tcDeclGroup ds                       = do
>   tyEnv0 <- getValueEnv
>   ctysLhs <- mapM tcDeclLhs ds
>   ctysRhs <- mapM (tcDeclRhs tyEnv0) ds
>   -- get all contexts
>   let cxsLhs = map fst ctysLhs
>       cxsRhs = map fst ctysRhs
>       tysRhs = map snd ctysRhs
>       cxs = zipWith (++) cxsLhs cxsRhs
>   sequence_ (zipWith3 unifyDecl ds ctysLhs ctysRhs)
>   theta <- getTypeSubst
>   let -- build the types and contexts of all declarations
>       types  = map (subst theta) tysRhs
>       cxs' = map (substContext theta) cxs
>       dsWithCxsAndTys = zip3 cxs' ds types
>   -- pass the inferred types to genDecl so that the contexts can be
>   -- renamed properly
>   mapM_ (genDecl (fvEnv (subst theta tyEnv0)) theta) dsWithCxsAndTys
>   -- do NOT return final contexts! TODO: return cxs or cxs' (or doesn't matter?)
>   return $ concat cxs

> --tcDeclGroup m tcEnv _ [ForeignDecl p cc _ f ty] =
> --  tcForeign m tcEnv p cc f ty

> --tcForeign :: ModuleIdent -> TCEnv -> Position -> CallConv -> Ident
> --               -> TypeExpr -> TCM ()
> --tcForeign m tcEnv p cc f ty =
> --  S.modify (bindFun m f (checkForeignType cc (expandPolyType tcEnv ty)))
> --  where checkForeignType CallConvPrimitive ty = ty
> --        checkForeignType CallConvCCall (ForAll n ty) =
> --          ForAll n (checkCCallType ty)
> --        checkCCallType (TypeArrow ty1 ty2)
> --          | isCArgType ty1 = TypeArrow ty1 (checkCCallType ty2)
> --          | otherwise = errorAt p (invalidCType "argument" m ty1)
> --        checkCCallType ty
> --          | isCResultType ty = ty
> --          | otherwise = errorAt p (invalidCType "result" m ty)
> --        isCArgType (TypeConstructor tc []) = tc `elem` basicTypeId
> --        isCArgType _ = False
> --        isCResultType (TypeConstructor tc []) = tc `elem` basicTypeId
> --        isCResultType (TypeConstructor tc [ty]) =
> --          tc == qIOId && (ty == unitType || isCArgType ty)
> --        isCResultType _ = False
> --        basicTypeId = [qBoolId,qCharId,qIntId,qFloatId]

> tcForeign :: Ident -> TypeExpr -> TCM ()
> tcForeign f ty = do
>   m <- getModuleIdent
>   tySc@(ForAll cx _ ty') <- expandPolyType (ST.emptyContext, ty)
>   modifyValueEnv $ bindFun m f (arrowArity ty') tySc

> tcExternal :: Ident -> TCM ()
> tcExternal f = do -- TODO is the semantic correct?
>   sigs <- getSigEnv
>   case lookupTypeSig f sigs of
>     Nothing -> internalError "TypeCheck.tcExternal"
>     Just (cx, ty) -> 
>       case cx of 
>         (ST.Context []) -> tcForeign f ty
>         _  -> internalError "TypeCheck.tcExternal doesn't have context"

> tcFree :: Ident -> TCM ()
> tcFree v = do
>   sigs <- getSigEnv
>   m  <- getModuleIdent
>   ty <- case lookupTypeSig v sigs of
>     Nothing -> freshTypeVar
>     Just t  -> do
>       ForAll cx n ty' <- expandPolyType t
>       unless (n == 0) $ report $ errPolymorphicFreeVar v
>       return ty'
>   modifyValueEnv $ bindFun m v (arrowArity ty) $ monoType ty

> tcDeclLhs :: Decl -> TCM ConstrType
> tcDeclLhs (FunctionDecl _ f _) = tcFunDecl f
> tcDeclLhs (PatternDecl  p t _) = tcPattern p t
> tcDeclLhs _ = internalError "TypeCheck.tcDeclLhs: no pattern match"

> tcFunDecl :: Ident -> TCM ConstrType
> tcFunDecl v = do
>   sigs <- getSigEnv
>   m <- getModuleIdent
>   (cx, ty) <- case lookupTypeSig v sigs of
>     Nothing -> freshConstrTypeVar
>     Just t  -> expandPolyType t >>= inst
>   modifyValueEnv $ bindFun m v (arrowArity ty) (monoType' (cx, ty))
>   return (cx, ty)

> tcDeclRhs :: ValueEnv -> Decl -> TCM ConstrType
> tcDeclRhs tyEnv0 (FunctionDecl _ f (eq:eqs)) = do
>   (cx0, ty0) <- tcEquation tyEnv0 eq
>   (cxs, ty)  <- tcEqns ty0 [] eqs
>   return (cx0 ++ cxs, ty)
>   where tcEqns :: Type -> BT.Context -> [Equation] -> TCM ConstrType
>         tcEqns ty cxs [] = return (cxs, ty)
>         tcEqns ty cxs (eq1@(Equation p _ _):eqs1)  = do
>           cty'@(cx', _ty') <- tcEquation tyEnv0 eq1
>           unify p "equation" (ppDecl (FunctionDecl p f [eq1])) (noContext ty) cty'
>           tcEqns ty (cx' ++ cxs) eqs1 
> tcDeclRhs tyEnv0 (PatternDecl _ _ rhs) = tcRhs tyEnv0 rhs
> tcDeclRhs _ _ = internalError "TypeCheck.tcDeclRhs: no pattern match"

> unifyDecl :: Decl -> ConstrType -> ConstrType -> TCM ()
> unifyDecl (FunctionDecl p f _) =
>   unify p "function binding" (text "Function:" <+> ppIdent f)
> unifyDecl (PatternDecl  p t _) =
>   unify p "pattern binding" (ppPattern 0 t)
> unifyDecl _ = internalError "TypeCheck.unifyDecl: no pattern match"

\end{verbatim}
In Curry we cannot generalize the types of let-bound variables because
they can refer to logic variables. Without this monomorphism
restriction unsound code like
\begin{verbatim}
bug = x =:= 1 & x =:= 'a'
  where x :: a
        x = fresh
fresh :: a
fresh = x where x free
\end{verbatim}
could be written. Note that \texttt{fresh} has the polymorphic type
$\forall\alpha.\alpha$. This is correct because \texttt{fresh} is a
function and therefore returns a different variable at each
invocation.

The code in \texttt{genVar} below also verifies that the inferred type
for a variable or function matches the type declared in a type
signature. As the declared type is already used for assigning an initial
type to a variable when it is used, the inferred type can only be more
specific. Therefore, if the inferred type does not match the type
signature the declared type must be too general.
\begin{verbatim}

> genDecl :: Set.Set Int -> TypeSubst -> (BT.Context, Decl, Type) -> TCM ()
> genDecl lvs theta (cx, FunctionDecl _ f (Equation _ lhs _ : _), inferredTy) = 
>   genVar True lvs theta arity cx inferredTy f
>   where arity = Just $ length $ snd $ flatLhs lhs
> genDecl lvs theta (cx, PatternDecl  _ t   _, inferredTy) = 
>   mapM_ (genVar False lvs theta Nothing cx inferredTy) (bv t)
> genDecl _ _ _ = internalError "TypeCheck.genDecl: no pattern match"

> genVar :: Bool -> Set.Set Int -> TypeSubst -> Maybe Int -> BT.Context -> Type -> Ident -> TCM ()
> genVar poly lvs theta ma cx infTy v = do
>   sigs <- getSigEnv
>   m <- getModuleIdent
>   tyEnv <- getValueEnv
>   let sigma0 = (genType poly $ subst theta $ varType v tyEnv)
>       arity  = fromMaybe (varArity v tyEnv) ma
>       -- build a mapping from the inferred type variables to the type
>       -- variables that appear in the newly instantiated type sigma0, 
>       -- so that the type variables in the inferred contexts can be
>       -- renamed properly
>       mapping = buildTypeVarsMapping infTy (typeSchemeToType sigma0) 
>       mapping' = map (\(n, n2) -> (n, TypeVariable n2)) mapping
>       shiftedContext = substContext (listToSubst mapping') cx
>       sigma = sigma0 `constrainBy` shiftedContext
>       ambTVs = ambiguousTypeVars shiftedContext
>   unless (null $ ambTVs) $ report (errAmbiguousTypeVars v ambTVs)  
>   case lookupTypeSig v sigs of
>     Nothing    -> modifyValueEnv $ rebindFun m v arity sigma
>     Just sigTy -> do
>       sigma' <- expandPolyType sigTy
>       -- TODO: consider contexts!
>       unless (eqTyScheme sigma sigma') $ report
>         $ errTypeSigTooGeneral (idPosition v) m what sigTy sigma
>       modifyValueEnv $ rebindFun m v arity sigma
>   where
>   what = text (if poly then "Function:" else "Variable:") <+> ppIdent v
>   genType poly' (ForAll _cx0 n ty)
>     | n > 0 = internalError $ "TypeCheck.genVar: " ++ showLine (idPosition v) ++ show v ++ " :: " ++ show ty
>     | poly' = gen lvs ty
>     | otherwise = monoType ty
>   eqTyScheme (ForAll _cx1 _ t1) (ForAll _cx2 _ t2) = equTypes t1 t2
>   ambiguousTypeVars :: BT.Context -> [Int]
>   ambiguousTypeVars = filter ( < 0) . concatMap (typeVars . snd)

> buildTypeVarsMapping :: Type -> Type -> [(Int, Int)]
> buildTypeVarsMapping t1 t2 = nub $ buildTypeVarsMapping' t1 t2

> buildTypeVarsMapping' :: Type -> Type -> [(Int, Int)]
> buildTypeVarsMapping' (TypeVariable n1) (TypeVariable n2) = [(n1, n2)]
> buildTypeVarsMapping' (TypeConstructor _ ts1) (TypeConstructor _ ts2)
>   = concat $ zipWith buildTypeVarsMapping' ts1 ts2
> buildTypeVarsMapping' (TypeArrow t11 t12) (TypeArrow t21 t22)
>   = buildTypeVarsMapping' t11 t21 ++ buildTypeVarsMapping' t12 t22
> buildTypeVarsMapping' (TypeConstrained _ _) (TypeConstrained _ _) = [] 
> buildTypeVarsMapping' (TypeSkolem _) (TypeSkolem _) = []
> buildTypeVarsMapping' (TypeRecord _ _) (TypeRecord _ _)
>   = internalError "buildTypeVarsMapping TODO"
> buildTypeVarsMapping' _ _ = internalError "types do not match in buildTypeVarsMapping"

> tcEquation :: ValueEnv -> Equation -> TCM ConstrType
> tcEquation tyEnv0 (Equation p lhs rhs) = do
>   tys <- mapM (tcPattern p) ts
>   (cx, ty) <- tcRhs tyEnv0 rhs
>   let cxs = concat $ map fst tys ++ [cx] 
>   checkSkolems p (text "Function: " <+> ppIdent f) tyEnv0
>                  (cxs, foldr TypeArrow ty (map getType tys))
>   where (f, ts) = flatLhs lhs

> tcLiteral :: Literal -> TCM ConstrType
> tcLiteral (Char   _ _) = return (BT.emptyContext, charType)
> tcLiteral (Int    v _)  = do --return intType
>   m  <- getModuleIdent
>   ty <- freshConstrained [intType, floatType]
>   modifyValueEnv $ bindFun m v (arrowArity ty) $ monoType ty
>   return (BT.emptyContext, ty)
> tcLiteral (Float  _ _) = return (BT.emptyContext, floatType)
> tcLiteral (String _ _) = return (BT.emptyContext, stringType)

> tcPattern :: Position -> Pattern -> TCM ConstrType
> tcPattern _ (LiteralPattern    l) = tcLiteral l
> tcPattern _ (NegativePattern _ l) = tcLiteral l
> tcPattern _ (VariablePattern   v) = do
>   sigs <- getSigEnv
>   (cx, ty) <- case lookupTypeSig v sigs of
>     Nothing -> freshConstrTypeVar
>     Just t  -> expandPolyType t >>= inst
>   tyEnv <- getValueEnv
>   m  <- getModuleIdent
>   maybe (modifyValueEnv (bindFun m v (arrowArity ty) (monoType' (cx, ty))) >> return (cx, ty))
>         (\ (ForAll cx0 _ t) -> return (cx0, t))
>         (sureVarType v tyEnv)
> tcPattern p t@(ConstructorPattern c ts) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- skol $ constrType m c tyEnv
>   liftM noContext $ unifyArgs (ppPattern 0 t) ts ty
>   where unifyArgs _   []       ty = return ty
>         unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) =
>           tcPattern p t1 >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty1) >>
>           unifyArgs doc ts1 ty2
>         unifyArgs _ _ _ = internalError "TypeCheck.tcPattern"
> tcPattern p t@(InfixPattern t1 op t2) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- skol (constrType m op tyEnv)
>   liftM noContext $ unifyArgs (ppPattern 0 t) [t1,t2] ty
>   where unifyArgs _ [] ty = return ty
>         unifyArgs doc (t':ts') (TypeArrow ty1 ty2) =
>           tcPattern p t' >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t')
>                 (noContext ty1) >>
>           unifyArgs doc ts' ty2
>         unifyArgs _ _ _ = internalError "TypeCheck.tcPattern"
> tcPattern p (ParenPattern t) = tcPattern p t
> tcPattern p (TuplePattern _ ts)
>  | null ts   = return $ noContext unitType
>  | otherwise = liftM (noContext . tupleType) $ mapM (\t -> liftM getType (tcPattern p t)) ts
> tcPattern p t@(ListPattern _ ts) =
>   freshTypeVar >>= flip (tcElems (ppPattern 0 t)) ts
>   where tcElems _ ty [] = return (noContext $ listType ty)
>         tcElems doc ty (t1:ts1) =
>           tcPattern p t1 >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty) >>
>           tcElems doc ty ts1
> tcPattern p t@(AsPattern v t') = do
>   ty1 <- tcPattern p (VariablePattern v)
>   ty2 <- tcPattern p t'
>   unify p "pattern" (ppPattern 0 t) ty1 ty2
>   return ty1
> tcPattern p (LazyPattern _ t) = tcPattern p t
> tcPattern p t@(FunctionPattern f ts) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   cEnv <- getClassEnv
>   ty <- inst (funType m f tyEnv cEnv) --skol (constrType m c tyEnv)
>   unifyArgs (ppPattern 0 t) ts (getType ty)
>   where unifyArgs _ [] ty = return $ noContext ty
>         unifyArgs doc (t1:ts1) ty@(TypeVariable _) = do
>              (alpha,beta) <- tcArrow p "function pattern" doc ty
>              ty' <- tcPatternFP p t1
>              unify p "function pattern"
>                    (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                    ty' (noContext alpha)
>              unifyArgs doc ts1 beta
>         unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) = do
>           tcPatternFP p t1 >>=
>             unify p "function pattern"
>                 (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty1) >>
>             unifyArgs doc ts1 ty2
>         unifyArgs _ _ ty = internalError $ "TypeCheck.tcPattern: " ++ show ty
> tcPattern p (InfixFuncPattern t1 op t2) =
>   tcPattern p (FunctionPattern op [t1,t2])
> tcPattern p r@(RecordPattern fs rt)
>   | isJust rt = do
>       m <- getModuleIdent
>       ty <- tcPattern p (fromJust rt)
>       fts <- mapM (tcFieldPatt tcPattern m) fs
>       let fts' = map (\(id0, ty0) -> (id0, getType ty0)) fts
>       alpha <- freshVar id
>       let rty = noContext $ TypeRecord fts' (Just alpha)
>       unify p "record pattern" (ppPattern 0 r) ty rty
>       return rty
>   | otherwise = do
>       m <- getModuleIdent
>       fts <- mapM (tcFieldPatt tcPattern m) fs
>       let fts' = map (\(id0, ty) -> (id0, getType ty)) fts
>       return (noContext $ TypeRecord fts' Nothing)

\end{verbatim}
In contrast to usual patterns, the type checking routine for arguments of
function patterns \texttt{tcPatternFP} differs from \texttt{tcPattern}
because of possibly multiple occurrences of variables.
\begin{verbatim}

> tcPatternFP :: Position -> Pattern -> TCM ConstrType
> tcPatternFP _ (LiteralPattern    l) = tcLiteral l
> tcPatternFP _ (NegativePattern _ l) = tcLiteral l
> tcPatternFP _ (VariablePattern v) = do
>   sigs <- getSigEnv
>   m <- getModuleIdent
>   cty@(cx, ty) <- case lookupTypeSig v sigs of
>     Nothing -> freshConstrTypeVar
>     Just t  -> expandPolyType t >>= inst
>   tyEnv <- getValueEnv
>   maybe (modifyValueEnv (bindFun m v (arrowArity ty) (monoType' cty)) >> return cty)
>         (\ (ForAll cx _ t) -> return (cx, t))
>         (sureVarType v tyEnv)
> tcPatternFP p t@(ConstructorPattern c ts) = do
>   m <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- skol (constrType m c tyEnv)
>   liftM noContext $ unifyArgs (ppPattern 0 t) ts ty
>   where unifyArgs _ [] ty = return ty
>         unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) = do
>           tcPatternFP p t1 >>=
>             unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty1) >>
>             unifyArgs doc ts1 ty2
>         unifyArgs _ _ _ = internalError "TypeCheck.tcPatternFP"
> tcPatternFP p t@(InfixPattern t1 op t2) = do
>   m <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- skol (constrType m op tyEnv)
>   liftM noContext $ unifyArgs (ppPattern 0 t) [t1,t2] ty
>   where unifyArgs _ [] ty = return ty
>         unifyArgs doc (t':ts') (TypeArrow ty1 ty2) = do
>           tcPatternFP p t' >>=
>             unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t')
>                   (noContext ty1) >>
>             unifyArgs doc ts' ty2
>         unifyArgs _ _ _ = internalError "TypeCheck.tcPatternFP"
> tcPatternFP p (ParenPattern t) = tcPatternFP p t
> tcPatternFP p (TuplePattern _ ts)
>  | null ts = return $ noContext unitType
>  | otherwise = liftM (noContext . tupleType) $ mapM (\t -> liftM getType $ tcPatternFP p t) ts
> tcPatternFP p t@(ListPattern _ ts) =
>   freshTypeVar >>= flip (tcElems (ppPattern 0 t)) ts
>   where tcElems _ ty [] = return (noContext $ listType ty)
>         tcElems doc ty (t1:ts1) =
>           tcPatternFP p t1 >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty) >>
>           tcElems doc ty ts1
> tcPatternFP p t@(AsPattern v t') =
>   do
>     ty1 <- tcPatternFP p (VariablePattern v)
>     ty2 <- tcPatternFP p t'
>     unify p "pattern" (ppPattern 0 t) ty1 ty2
>     return ty1
> tcPatternFP p (LazyPattern _ t) = tcPatternFP p t
> tcPatternFP p t@(FunctionPattern f ts) = do
>     m <- getModuleIdent
>     tyEnv <- getValueEnv
>     cEnv <- getClassEnv
>     ty <- inst (funType m f tyEnv cEnv) --skol (constrType m c tyEnv)
>     unifyArgs (ppPattern 0 t) ts (getType ty)
>   where unifyArgs _ [] ty = return $ noContext ty
>         unifyArgs doc (t1:ts1) ty@(TypeVariable _) = do
>              (alpha,beta) <- tcArrow p "function pattern" doc ty
>              ty' <- tcPatternFP p t1
>              unify p "function pattern"
>                    (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                    ty' (noContext alpha)
>              unifyArgs doc ts1 beta
>         unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) =
>           tcPatternFP p t1 >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty1) >>
>           unifyArgs doc ts1 ty2
>         unifyArgs _ _ _ = internalError "TypeCheck.tcPatternFP"
> tcPatternFP p (InfixFuncPattern t1 op t2) =
>   tcPatternFP p (FunctionPattern op [t1,t2])
> tcPatternFP p r@(RecordPattern fs rt)
>   | isJust rt = do
>       m <- getModuleIdent
>       ty <- tcPatternFP p (fromJust rt)
>       fts <- mapM (tcFieldPatt tcPatternFP m) fs
>       let fts' = map (\(id0, ty0) -> (id0, getType ty0)) fts
>       alpha <- freshVar id
>       let rty = noContext $ TypeRecord fts' (Just alpha)
>       unify p "record pattern" (ppPattern 0 r) ty rty
>       return rty
>   | otherwise = do
>       m <- getModuleIdent
>       fts <- mapM (tcFieldPatt tcPatternFP m) fs
>       let fts' = map (\(id0, ty) -> (id0, getType ty)) fts
>       return (noContext $ TypeRecord fts' Nothing)

> tcFieldPatt :: (Position -> Pattern -> TCM ConstrType) -> ModuleIdent
>             -> Field Pattern -> TCM (Ident, ConstrType)
> tcFieldPatt tcPatt m f@(Field _ l t) = do
>     tyEnv <- getValueEnv
>     let p = idPosition l
>     lty <- maybe (freshTypeVar
>                    >>= (\lty' ->
>                          modifyValueEnv
>                            (bindLabel l (qualifyWith m (mkIdent "#Rec"))
>                                       (polyType lty'))
>                          >> return (noContext lty')))
>                  (\ (ForAll cx _ lty') -> return (cx, lty'))
>                  (sureLabelType l tyEnv)
>     ty <- tcPatt p t
>     unify p "record" (text "Field:" <+> ppFieldPatt f) lty ty
>     return (l,ty)

> tcRhs ::ValueEnv -> Rhs -> TCM ConstrType
> tcRhs tyEnv0 (SimpleRhs p e ds) = do
>   cxs <- tcDecls ds
>   (cx, ty) <- tcExpr p e
>   checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cx ++ cxs, ty)
> tcRhs tyEnv0 (GuardedRhs es ds) = do
>   cxs <- tcDecls ds
>   (cxs', ty) <- tcCondExprs tyEnv0 es
>   return (cxs ++ cxs', ty)

> tcCondExprs :: ValueEnv -> [CondExpr] -> TCM ConstrType
> tcCondExprs tyEnv0 es = do
>   gty <- if length es > 1 then return $ noContext boolType
>                           else liftM noContext $ freshConstrained [successType,boolType]
>   ty <- freshConstrTypeVar
>   tcCondExprs' gty ty es
>   where tcCondExprs' _   ty [] = return ty
>         tcCondExprs' gty ty (e1:es1) =
>           tcCondExpr gty ty e1 >> tcCondExprs' gty ty es1
>         tcCondExpr gty ty (CondExpr p g e) = do
>           tcExpr p g >>=
>             unify p "guard" (ppExpr 0 g) gty >>
>             tcExpr p e >>=
>             checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 >>=
>             unify p "guarded expression" (ppExpr 0 e) ty

> tcExpr :: Position -> Expression -> TCM ConstrType
> tcExpr _ (Literal     l) = tcLiteral l
> tcExpr _ (Variable    v)
>     -- anonymous free variable
>   | isAnonId v' = do
>       m <- getModuleIdent
>       ty <- freshTypeVar
>       modifyValueEnv $ bindFun m v' (arrowArity ty) $ monoType ty
>       return $ noContext ty
>   | otherwise    = do
>       sigs <- getSigEnv
>       m <- getModuleIdent
>       cEnv <- getClassEnv
>       case qualLookupTypeSig m v sigs of
>         Just ty -> expandPolyType ty >>= inst
>         Nothing -> getValueEnv >>= inst . (flip (funType m v) cEnv)
>   where v' = unqualify v
> tcExpr _ (Constructor c) = do
>  m <- getModuleIdent
>  getValueEnv >>= instExist . constrType m c
> tcExpr p (Typed e cx sig) = do
>   m <- getModuleIdent
>   tyEnv0 <- getValueEnv
>   cty <- tcExpr p e
>   sigma' <- expandPolyType (cx, sig')
>   inst sigma' >>= flip (unify p "explicitly typed expression" (ppExpr 0 e)) cty
>   theta <- getTypeSubst
>   -- TODO: consider contexts!
>   let sigma  = gen (fvEnv (subst theta tyEnv0)) (subst theta (getType cty))
>   unless (sigma == sigma') 
>     (report $ errTypeSigTooGeneral p m (text "Expression:" <+> ppExpr 0 e) (cx, sig') sigma)
>   return cty
>   where sig' = nameSigType sig
> tcExpr p (Paren e) = tcExpr p e
> tcExpr p (Tuple _ es)
>   | null es = return $ noContext unitType
>   | otherwise = do 
>      ctys <- mapM (tcExpr p) es
>      let cx = concatMap fst ctys
>      let tys = map snd ctys
>      return (cx, tupleType tys)
> tcExpr p e@(List _ es) = freshConstrTypeVar >>= tcElems (ppExpr 0 e) es
>   where tcElems :: Doc -> [Expression] -> ConstrType -> TCM ConstrType
>         tcElems _ [] (cx, ty) = return (cx, listType ty)
>         tcElems doc (e1:es1) cty@(cx, ty) = do
>           cty'@(cx', _ty') <- tcExpr p e1
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e1)
>                 cty cty'
>           tcElems doc es1 (cx ++ cx', ty)
> tcExpr p (ListCompr _ e qs) = do
>     tyEnv0 <- getValueEnv
>     cxs <- concatMapM (tcQual p) qs
>     (cx, ty) <- tcExpr p e
>     checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cx ++ cxs, listType ty)
> tcExpr p e@(EnumFrom e1) = do
>     cty1@(cx1, _ty1) <- tcExpr p e1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     return (cx1, listType intType)
> tcExpr p e@(EnumFromThen e1 e2) = do
>     cty1@(cx1, _ty1) <- tcExpr p e1
>     cty2@(cx2, _ty2) <- tcExpr p e2
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) (noContext intType) cty2
>     return (cx1 ++ cx2, listType intType)
> tcExpr p e@(EnumFromTo e1 e2) = do
>     cty1@(cx1, _ty1) <- tcExpr p e1
>     cty2@(cx2, _ty2) <- tcExpr p e2
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) (noContext intType) cty2
>     return (cx1 ++ cx2, listType intType)
> tcExpr p e@(EnumFromThenTo e1 e2 e3) = do
>     cty1@(cx1, _ty1) <- tcExpr p e1
>     cty2@(cx2, _ty2) <- tcExpr p e2
>     cty3@(cx3, _ty3) <- tcExpr p e3
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) (noContext intType) cty2
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) (noContext intType) cty3
>     return (cx1 ++ cx2 ++ cx3, listType intType)
> tcExpr p e@(UnaryMinus op e1) = do
>     opTy <- opType op
>     cty1 <- tcExpr p e1
>     unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           opTy cty1
>     return cty1
>   where opType op'
>           | op' == minusId  = liftM noContext $ freshConstrained [intType,floatType]
>           | op' == fminusId = return $ noContext floatType
>           | otherwise = internalError $ "TypeCheck.tcExpr unary " ++ idName op'
> tcExpr p e@(Apply e1 e2) = do
>     (cx1,       ty1) <- tcExpr p e1
>     cty2@(cx2, _ty2) <- tcExpr p e2
>     (alpha,beta) <- 
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>              ty1
>     unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>           (noContext alpha) cty2
>     cx' <- adjustContext (cx1 ++ cx2)
>     return (cx', beta)
> tcExpr p e@(InfixApply e1 op e2) = do
>     (cxo, opTy)      <- tcExpr p (infixOp op)
>     cty1@(cx1, _ty1) <- tcExpr p e1
>     cty2@(cx2, _ty2) <- tcExpr p e2
>     (alpha,beta,gamma) <-
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) opTy
>     unify p "infix application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext alpha) cty1
>     unify p "infix application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>           (noContext beta) cty2
>     cx' <- adjustContext (cxo ++ cx1 ++ cx2)
>     return (cx', gamma)
> tcExpr p e@(LeftSection e1 op) = do
>     opTy@(cxo, _) <- tcExpr p (infixOp op)
>     cty1@(cx1, _) <- tcExpr p e1
>     (alpha,beta) <-
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               (getType opTy)
>     unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext alpha) cty1
>     cx' <- adjustContext (cxo ++ cx1)
>     return (cx', beta)
> tcExpr p e@(RightSection op e1) = do
>     opTy@(cxo, _) <- tcExpr p (infixOp op)
>     cty1@(cx1, _) <- tcExpr p e1
>     (alpha,beta,gamma) <-
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) (getType opTy)
>     unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext beta) cty1
>     cx' <- adjustContext (cxo ++ cx1)
>     return (cx', TypeArrow alpha gamma)
> tcExpr p expr@(Lambda _ ts e) = do
>     tyEnv0 <- getValueEnv
>     ctys <- mapM (tcPattern p) ts
>     (cx, ty) <- tcExpr p e
>     let cxs = concat (map fst ctys ++ [cx]) 
>     checkSkolems p (text "Expression:" <+> ppExpr 0 expr) tyEnv0
>                    (cxs, foldr TypeArrow ty (map getType ctys))
> tcExpr p (Let ds e) = do
>     tyEnv0 <- getValueEnv
>     cxs <- tcDecls ds
>     (cx, ty) <- tcExpr p e
>     -- We gather all contexts, also in the case that a declaration isn't 
>     -- used at all (neither directly nor indirectly). But whether this 
>     -- is the case is not trivially determinable (TODO!).  
>     checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cx ++ cxs, ty)
> tcExpr p (Do sts e) = do
>     tyEnv0 <- getValueEnv
>     cxs <- concatMapM (tcStmt p) sts
>     alpha <- freshTypeVar
>     cty@(cx, ty) <- tcExpr p e
>     unify p "statement" (ppExpr 0 e) (noContext $ ioType alpha) cty
>     checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cxs ++ cx, ty)
> tcExpr p e@(IfThenElse _ e1 e2 e3) = do
>     cty1@(cx1, _ty1) <- tcExpr p e1
>     unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext boolType) cty1
>     cty2@(cx2, _ty2) <- tcExpr p e2
>     cty3@(cx3, ty3)  <- tcExpr p e3
>     unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>           cty2 cty3
>     return (cx1 ++ cx2 ++ cx3, ty3)
> tcExpr p (Case _ _ e alts) = do
>     tyEnv0 <- getValueEnv
>     cty@(cx, _) <- tcExpr p e
>     alpha <- freshConstrTypeVar
>     (cxA, tyA) <- tcAlts tyEnv0 cty alpha [] alts
>     return (cx ++ cxA, tyA)
>   where tcAlts _      _   (_, ty2) cx [] = return (cx, ty2)
>         tcAlts tyEnv0 ty1 ty2 cx (alt1:alts1) = do
>           cx1 <- tcAlt (ppAlt alt1) tyEnv0 ty1 ty2 alt1
>           tcAlts tyEnv0 ty1 ty2 (cx ++ cx1) alts1
>         tcAlt doc tyEnv0 ty1 ty2 (Alt p1 t rhs) = do
>           ctyP@(cxP, _) <- tcPattern p1 t
>           unify p1 "case pattern" (doc $-$ text "Term:" <+> ppPattern 0 t)
>                 ty1 ctyP
>           ctyRhs@(cxRhs, _) <- tcRhs tyEnv0 rhs
>           unify p1 "case branch" doc ty2 ctyRhs
>           return (cxP ++ cxRhs)
> tcExpr _ (RecordConstr fs) = do
>     fts <- mapM tcFieldExpr fs
>     let cxs = concatMap (fst . snd) fts
>     return (cxs, TypeRecord 
>       (map (\(id0, cty) -> (id0, getType cty)) fts) Nothing)
> tcExpr p r@(RecordSelection e l) = do
>     m <- getModuleIdent
>     cty@(cx, _) <- tcExpr p e
>     tyEnv <- getValueEnv
>     lty <- maybe (freshTypeVar
>                    >>= (\lty' ->
>                          modifyValueEnv
>                            (bindLabel l (qualifyWith m (mkIdent "#Rec"))
>                                       (monoType lty'))
>                          >> return lty'))
>                  -- TODO: ignore context?
>                  (\ (ForAll _cx _ lty') -> return lty')
>                  (sureLabelType l tyEnv)
>     alpha <- freshVar id
>     let rty = TypeRecord [(l,lty)] (Just alpha)
>     unify p "record selection" (ppExpr 0 r) cty (noContext rty)
>     -- TODO: adjusting context, because we have a situation similar to
>     -- Apply (?)
>     cx' <- adjustContext cx
>     return (cx', lty)
> tcExpr p r@(RecordUpdate fs e) = do
>     ty    <- tcExpr p e
>     fts   <- mapM tcFieldExpr fs
>     alpha <- freshVar id
>     let rty = TypeRecord (map (\(id0, cty) -> (id0, getType cty)) fts) (Just alpha)
>     unify p "record update" (ppExpr 0 r) ty (noContext rty)
>     return ty

> tcQual :: Position -> Statement -> TCM BT.Context
> tcQual p (StmtExpr     _ e) = do
>   cty@(cx, _ty) <- tcExpr p e
>   unify p "guard" (ppExpr 0 e) (noContext boolType) cty
>   return cx
> tcQual p q@(StmtBind _ t e) = do
>   (cx1,      ty1) <- tcPattern p t
>   cty2@(cx2, _  ) <- tcExpr p e
>   -- TODO: return contexts
>   unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>         (noContext $ listType ty1) cty2
>   return (cx1 ++ cx2)
> tcQual _ (StmtDecl      ds) = tcDecls ds

> tcStmt ::Position -> Statement -> TCM BT.Context
> tcStmt p (StmtExpr _ e) = do
>   alpha       <- freshTypeVar
>   cty@(cx, _) <- tcExpr p e
>   unify p "statement" (ppExpr 0 e) (noContext $ ioType alpha) cty
>   return cx
> tcStmt p st@(StmtBind _ t e) = do
>   cty1@(cx1, _) <- tcPattern p t
>   cty2@(cx2, _) <- tcExpr p e
>   unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e) (noContext $ ioType $ getType cty1) cty2
>   return (cx1 ++ cx2)
> tcStmt _ (StmtDecl ds) = tcDecls ds

> tcFieldExpr :: Field Expression -> TCM (Ident, ConstrType)
> tcFieldExpr f@(Field _ l e) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   let p = idPosition l
>   lty <- maybe (freshTypeVar
>                >>= (\lty' ->
>                      modifyValueEnv (bindLabel l (qualifyWith m (mkIdent "#Rec"))
>                                     (monoType lty'))
>                >> (return $ noContext lty')))
>                  inst
>         (sureLabelType l tyEnv)
>   cty <- tcExpr p e
>   unify p "record" (text "Field:" <+> ppFieldExpr f) lty cty
>   return (l,cty)

> adjustContext :: BT.Context -> TCM BT.Context
> adjustContext cxs = do
>   theta <- getTypeSubst
>   return (substContext theta cxs) 

\end{verbatim}
The function \texttt{tcArrow} checks that its argument can be used as
an arrow type $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$. Similarly, the function \texttt{tcBinary} checks
that its argument can be used as an arrow type
$\alpha\rightarrow\beta\rightarrow\gamma$ and returns the triple
$(\alpha,\beta,\gamma)$.
\begin{verbatim}

> tcArrow :: Position -> String -> Doc -> Type -> TCM (Type, Type)
> tcArrow p what doc ty = do
>   theta <- getTypeSubst
>   unaryArrow (subst theta ty)
>   where
>   unaryArrow (TypeArrow ty1 ty2) = return (ty1, ty2)
>   unaryArrow (TypeVariable   tv) = do
>     alpha <- freshTypeVar
>     beta  <- freshTypeVar
>     modifyTypeSubst $ bindVar tv $ TypeArrow alpha beta
>     return (alpha, beta)
>   unaryArrow ty'                 = do
>     m <- getModuleIdent
>     report $ errNonFunctionType p what doc m ty'
>     liftM2 (,) freshTypeVar freshTypeVar

> tcBinary :: Position -> String -> Doc -> Type -> TCM (Type, Type, Type)
> tcBinary p what doc ty = tcArrow p what doc ty >>= uncurry binaryArrow
>   where
>   binaryArrow ty1 (TypeArrow ty2 ty3) = return (ty1, ty2, ty3)
>   binaryArrow ty1 (TypeVariable   tv) = do
>     beta  <- freshTypeVar
>     gamma <- freshTypeVar
>     modifyTypeSubst $ bindVar tv $ TypeArrow beta gamma
>     return (ty1, beta, gamma)
>   binaryArrow ty1 ty2 = do
>     m <- getModuleIdent
>     report $ errNonBinaryOp p what doc m (TypeArrow ty1 ty2)
>     liftM3 (,,) (return ty1) freshTypeVar freshTypeVar

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> ConstrType -> ConstrType -> TCM ()
> unify p what doc (_, ty1) (_, ty2) = do
>   theta <- getTypeSubst
>   let ty1' = subst theta ty1
>   let ty2' = subst theta ty2
>   m <- getModuleIdent
>   case unifyTypes m ty1' ty2' of
>     Left reason -> report $ errTypeMismatch p what doc m ty1' ty2' reason
>     Right sigma -> modifyTypeSubst (compose sigma)

> unifyTypes :: ModuleIdent -> Type -> Type -> Either Doc TypeSubst
> unifyTypes _ (TypeVariable tv1) (TypeVariable tv2)
>   | tv1 == tv2            = Right idSubst
>   | otherwise             = Right (singleSubst tv1 (TypeVariable tv2))
> unifyTypes m (TypeVariable tv) ty
>   | tv `elem` typeVars ty = Left  (errRecursiveType m tv ty)
>   | otherwise             = Right (singleSubst tv ty)
> unifyTypes m ty (TypeVariable tv)
>   | tv `elem` typeVars ty = Left  (errRecursiveType m tv ty)
>   | otherwise             = Right (singleSubst tv ty)
> unifyTypes _ (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2)
>   | tv1  == tv2           = Right idSubst
>   | tys1 == tys2          = Right (singleSubst tv1 (TypeConstrained tys2 tv2))
> unifyTypes m (TypeConstrained tys tv) ty =
>   foldr (choose . unifyTypes m ty) (Left (errIncompatibleTypes m ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes m ty (TypeConstrained tys tv) =
>   foldr (choose . unifyTypes m ty) (Left (errIncompatibleTypes m ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes m (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = unifyTypeLists m tys1 tys2
> unifyTypes m (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   unifyTypeLists m [ty11, ty12] [ty21, ty22]
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Right idSubst
> unifyTypes m (TypeRecord fs1 Nothing) tr2@(TypeRecord fs2 Nothing)
>   | length fs1 == length fs2 = unifyTypedLabels m fs1 tr2
> unifyTypes m tr1@(TypeRecord _ Nothing) (TypeRecord fs2 (Just a2)) =
>   either Left
>          (\res -> either Left
>                          (Right . compose res)
>                          (unifyTypes m (TypeVariable a2) tr1))
>          (unifyTypedLabels m fs2 tr1)
> unifyTypes m tr1@(TypeRecord _ (Just _)) tr2@(TypeRecord _ Nothing) =
>   unifyTypes m tr2 tr1
> unifyTypes m (TypeRecord fs1 (Just a1)) tr2@(TypeRecord fs2 (Just a2)) =
>   let (fs1', rs1, rs2) = splitFields fs1 fs2
>   in  either
>         Left
>         (\res ->
>           either
>             Left
>             (\res' -> Right (compose res res'))
>             (unifyTypeLists m [TypeVariable a1,
>                                TypeRecord (fs1 ++ rs2) Nothing]
>                               [TypeVariable a2,
>                                TypeRecord (fs2 ++ rs1) Nothing]))
>         (unifyTypedLabels m fs1' tr2)
>   where
>   splitFields fsx fsy = split' [] [] fsy fsx
>   split' fs1' rs1 rs2 [] = (fs1',rs1,rs2)
>   split' fs1' rs1 rs2 ((l,ty):ltys) =
>     maybe (split' fs1' ((l,ty):rs1) rs2 ltys)
>           (const (split' ((l,ty):fs1') rs1 (remove l rs2) ltys))
>           (lookup l rs2)
> unifyTypes m ty1 ty2 = Left (errIncompatibleTypes m ty1 ty2)

> unifyTypeLists :: ModuleIdent -> [Type] -> [Type] -> Either Doc TypeSubst
> unifyTypeLists _ []          _             = Right idSubst
> unifyTypeLists _ _           []            = Right idSubst
> unifyTypeLists m (ty1 : tys1) (ty2 : tys2) =
>   either Left unifyTypesTheta (unifyTypeLists m tys1 tys2)
>   where unifyTypesTheta theta =
>           either Left (Right . flip compose theta)
>                  (unifyTypes m (subst theta ty1) (subst theta ty2))

> unifyTypedLabels :: ModuleIdent -> [(Ident,Type)] -> Type -> Either Doc TypeSubst
> unifyTypedLabels _ [] (TypeRecord _ _) = Right idSubst
> unifyTypedLabels m ((l,ty):fs1) tr@(TypeRecord fs2 _) =
>   either Left
>          (\r ->
>            maybe (Left (errMissingLabel m l tr))
>                  (\ty' ->
>                    either (const (Left (errIncompatibleLabelTypes m l ty ty')))
>                           (Right . flip compose r)
>                           (unifyTypes m ty ty'))
>                  (lookup l fs2))
>          (unifyTypedLabels m fs1 tr)
> unifyTypedLabels _ _ _ = internalError "TypeCheck.unifyTypedLabels"

\end{verbatim}
For each declaration group, the type checker has to ensure that no
skolem type escapes its scope.
\begin{verbatim}

> checkSkolems :: Position -> Doc -> ValueEnv -> ConstrType -> TCM ConstrType
> checkSkolems p what tyEnv (cx, ty) = do
>   m     <- getModuleIdent
>   theta <- getTypeSubst
>   let ty' = subst theta ty
>       fs  = fsEnv $ subst theta tyEnv
>   unless (all (`Set.member` fs) $ typeSkolems ty') $
>            report $ errSkolemEscapingScope p m what ty'
>   return (cx, ty')

\end{verbatim}
\paragraph{Instantiation and Generalization}
We use negative offsets for fresh type variables.
\begin{verbatim}

> fresh :: (Int -> a) -> TCM a
> fresh f = f `liftM` getNextId

> freshVar :: (Int -> a) -> TCM a
> freshVar f = fresh $ \ n -> f (- n - 1)

> freshTypeVar :: TCM Type
> freshTypeVar = freshVar TypeVariable

> freshConstrTypeVar :: TCM ConstrType
> freshConstrTypeVar = do ftvar <- freshTypeVar; return (BT.emptyContext, ftvar)

> freshConstrained :: [Type] -> TCM Type
> freshConstrained = freshVar . TypeConstrained

> freshSkolem :: TCM Type
> freshSkolem = fresh TypeSkolem

> inst :: TypeScheme -> TCM ConstrType
> inst (ForAll cx n ty) = do
>   tys <- replicateM n freshTypeVar
>   let cx' = instContext tys cx
>   return $ (cx', expandAliasType tys ty)

> instContext :: [Type] -> BT.Context -> BT.Context
> instContext tys cx = map convert cx
>   where 
>     convert (qid, y) = (qid, convertType y)
>     convertType (TypeVariable x) 
>       = if x < 0 
>         then {-internalError "instContext" -} TypeVariable x
>         else if x >= length tys
>              then internalError ("instContext too big " ++ show x)
>              else tys !! x
>     convertType (TypeConstructor tcon ts) 
>       = TypeConstructor tcon (map convertType ts) 
>     convertType (TypeArrow t1 t2) 
>       = TypeArrow (convertType t1) (convertType t2)
>     convertType (TypeConstrained ts n) 
>       = TypeConstrained (map convertType ts) n
>     convertType (TypeSkolem n) = TypeSkolem n
>     convertType (TypeRecord ts n) = 
>       TypeRecord (map (\(id0, t) -> (id0, convertType t)) ts) n
   

> instExist :: ExistTypeScheme -> TCM ConstrType
> instExist (ForAllExist cx n n' ty) = do
>   tys <- replicateM (n + n') freshTypeVar
>   let cx' = instContext tys cx
>   return $ (cx', expandAliasType tys ty) 

> skol :: ExistTypeScheme -> TCM Type
> skol (ForAllExist cx n n' ty) = do
>   tys  <- replicateM n  freshTypeVar
>   tys' <- replicateM n' freshSkolem
>   -- let cx' = instContext (tys ++ tys') cx
>   return $ ({-cx',-} expandAliasType (tys ++ tys') ty)

> gen :: Set.Set Int -> Type -> TypeScheme
> gen gvs ty = ForAll BT.emptyContext (length tvs)
>                     (subst (foldr2 bindSubst idSubst tvs tvs') ty)
>   where tvs = [tv | tv <- nub (typeVars ty), tv `Set.notMember` gvs]
>         tvs' = map TypeVariable [0 ..]

\end{verbatim}
\paragraph{Auxiliary Functions}
The functions \texttt{constrType}, \texttt{varType}, and
\texttt{funType} are used to retrieve the type of constructors,
pattern variables, and variables in expressions, respectively, from
the type environment. Because the syntactical correctness has already
been verified by the syntax checker, none of these functions should
fail.

Note that \texttt{varType} can handle ambiguous identifiers and
returns the first available type. This function is used for looking up
the type of an identifier on the left hand side of a rule where it
unambiguously refers to the local definition.
\begin{verbatim}

> constrType :: ModuleIdent -> QualIdent -> ValueEnv -> ExistTypeScheme
> constrType m c tyEnv = case qualLookupValue c tyEnv of
>   [DataConstructor  _ _ sigma] -> sigma
>   [NewtypeConstructor _ sigma] -> sigma
>   _ -> case qualLookupValue (qualQualify m c) tyEnv of
>     [DataConstructor  _ _ sigma] -> sigma
>     [NewtypeConstructor _ sigma] -> sigma
>     _ -> internalError $ "TypeCheck.constrType " ++ show c

> varArity :: Ident -> ValueEnv -> Int
> varArity v tyEnv = case lookupValue v tyEnv of
>   Value _ a _ : _ -> a
>   _ -> internalError $ "TypeCheck.varArity " ++ show v

> varType :: Ident -> ValueEnv -> TypeScheme
> varType v tyEnv = case lookupValue v tyEnv of
>   Value _ _ sigma : _ -> sigma
>   _ -> internalError $ "TypeCheck.varType " ++ show v

> sureVarType :: Ident -> ValueEnv -> Maybe TypeScheme
> sureVarType v tyEnv = case lookupValue v tyEnv of
>   Value _ _ sigma : _ -> Just sigma
>   _ -> Nothing

> funType :: ModuleIdent -> QualIdent -> ValueEnv -> ClassEnv -> TypeScheme
> funType m f tyEnv cEnv = case qualLookupValue f tyEnv of
>   [Value _ _ sigma] -> sigma
>   _ -> case qualLookupValue (qualQualify m f) tyEnv of
>     [Value _ _ sigma] -> sigma
>     _ -> case lookupMethodTypeScheme cEnv f of
>        Just tsc -> tsc -- TODO: add instance context
>        Nothing -> internalError $ "TypeCheck.funType " ++ show f ++ ", more precisely " ++ show (unqualify f)

> sureLabelType :: Ident -> ValueEnv -> Maybe TypeScheme
> sureLabelType l tyEnv = case lookupValue l tyEnv of
>   Label _ _ sigma : _ -> Just sigma
>   _ -> Nothing

\end{verbatim}
The function \texttt{expandType} expands all type synonyms in a type
and also qualifies all type constructors with the name of the module
in which the type was defined.
\begin{verbatim}

> type ConstrType = (BT.Context, Type)

> noContext :: Type -> ConstrType
> noContext ty = (BT.emptyContext, ty)

> getType :: ConstrType -> Type
> getType (_cx, type0) = type0

> expandPolyType :: BaseConstrType -> TCM TypeScheme
> expandPolyType ty 
>   = (\(cx, ty0) -> (polyType (normalize ty0) `constrainBy` cx)) `liftM` expandMonoType [] ty

> expandMonoType :: [Ident] -> BaseConstrType -> TCM ConstrType
> expandMonoType tvs ty = do
>   m <- getModuleIdent
>   tcEnv <- getTyConsEnv
>   return $ expandMonoType' m tcEnv tvs ty

> expandMonoType' :: ModuleIdent -> TCEnv -> [Ident] -> BaseConstrType -> ConstrType
> expandMonoType' m tcEnv tvs ty = (cx, expandType m tcEnv ty')
>   where (cx, ty') = (toConstrType tvs ty)

> expandMonoTypes :: ModuleIdent -> TCEnv -> [Ident] -> [BaseConstrType] -> [ConstrType]
> expandMonoTypes m tcEnv tvs tys 
>   = map (\(cx, ty) -> (cx, expandType m tcEnv ty)) (toConstrTypes tvs tys)

> expandType :: ModuleIdent -> TCEnv -> Type -> Type
> expandType m tcEnv (TypeConstructor tc tys) = case qualLookupTC tc tcEnv of
>   [DataType     tc' _  _] -> TypeConstructor tc' tys'
>   [RenamingType tc' _  _] -> TypeConstructor tc' tys'
>   [AliasType    _   _ ty] -> expandAliasType tys' ty
>   _ -> case qualLookupTC (qualQualify m tc) tcEnv of
>     [DataType     tc' _ _ ] -> TypeConstructor tc' tys'
>     [RenamingType tc' _ _ ] -> TypeConstructor tc' tys'
>     [AliasType    _   _ ty] -> expandAliasType tys' ty
>     _ -> internalError $ "TypeCheck.expandType " ++ show tc
>   where tys' = map (expandType m tcEnv) tys
> expandType _ _     tv@(TypeVariable      _) = tv
> expandType _ _     tc@(TypeConstrained _ _) = tc
> expandType m tcEnv (TypeArrow      ty1 ty2) =
>   TypeArrow (expandType m tcEnv ty1) (expandType m tcEnv ty2)
> expandType _ _     ts@(TypeSkolem        _) = ts
> expandType m tcEnv (TypeRecord       fs rv) =
>   TypeRecord (map (\ (l, ty) -> (l, expandType m tcEnv ty)) fs) rv

\end{verbatim}
The functions \texttt{fvEnv} and \texttt{fsEnv} compute the set of
free type variables and free skolems of a type environment,
respectively. We ignore the types of data constructors here because we
know that they are closed.
\begin{verbatim}

> fvEnv :: ValueEnv -> Set.Set Int
> fvEnv tyEnv = Set.fromList
>   [tv | ty <- localTypes tyEnv, tv <- typeVars ty, tv < 0]

> fsEnv :: ValueEnv -> Set.Set Int
> fsEnv = Set.unions . map (Set.fromList . typeSkolems) . localTypes

> localTypes :: ValueEnv -> [Type]
> localTypes tyEnv = [ty | (_, Value _ _ (ForAll cx _ ty)) <- localBindings tyEnv]

\end{verbatim}
Miscellaneous functions.
\begin{verbatim}

> remove :: Eq a => a -> [(a, b)] -> [(a, b)]
> remove _ []         = []
> remove k (kv : kvs)
>   | k == fst kv     = kvs
>   | otherwise       = kv : remove k kvs

\end{verbatim}
Error functions.
\begin{verbatim}

> errRecursiveTypes :: [Ident] -> Message
> errRecursiveTypes []         = internalError
>   "TypeCheck.recursiveTypes: empty list"
> errRecursiveTypes [tc]       = posMessage tc $ hsep $ map text
>   ["Recursive synonym type", idName tc]
> errRecursiveTypes (tc : tcs) = posMessage tc $
>   text "Recursive synonym types" <+> text (idName tc) <+> types empty tcs
>   where
>   types _    []         = empty
>   types comm [tc1]      = comm <+> text "and" <+> text (idName tc1)
>                           <+> parens (text $ showLine $ idPosition tc1)
>   types _    (tc1:tcs1) = comma <+> text (idName tc1) <+>
>                           parens (text $ showLine $ idPosition tc1)
>                           <> types comma tcs1

> errPolymorphicFreeVar :: Ident -> Message
> errPolymorphicFreeVar v = posMessage v $ hsep $ map text
>   ["Free variable", idName v, "has a polymorphic type"]

> errTypeSigTooGeneral :: Position -> ModuleIdent -> Doc -> BaseConstrType -> TypeScheme
>                      -> Message
> errTypeSigTooGeneral p m what (cx, ty) sigma = posMessage p $ vcat
>   [ text "Type signature too general", what
>   , text "Inferred type:"  <+> ppTypeScheme m sigma
>   , text "Type signature:" <+> parens (ppContext cx) <+> text "=>" <+> ppTypeExpr 0 ty
>   ]

> errNonFunctionType :: Position -> String -> Doc -> ModuleIdent -> Type -> Message
> errNonFunctionType p what doc m ty = posMessage p $ vcat
>   [ text "Type error in" <+> text what, doc
>   , text "Type:" <+> ppType m ty
>   , text "Cannot be applied"
>   ]

> errNonBinaryOp :: Position -> String -> Doc -> ModuleIdent -> Type -> Message
> errNonBinaryOp p what doc m ty = posMessage p $ vcat
>   [ text "Type error in" <+> text what, doc
>   , text "Type:" <+> ppType m ty
>   , text "Cannot be used as binary operator"
>   ]

> errTypeMismatch :: Position -> String -> Doc -> ModuleIdent -> Type -> Type -> Doc
>                 -> Message
> errTypeMismatch p what doc m ty1 ty2 reason = posMessage p $ vcat
>   [ text "Type error in"  <+> text what, doc
>   , text "Inferred type:" <+> ppType m ty2
>   , text "Expected type:" <+> ppType m ty1
>   , reason
>   ]

> errSkolemEscapingScope :: Position -> ModuleIdent -> Doc -> Type -> Message
> errSkolemEscapingScope p m what ty = posMessage p $ vcat
>   [ text "Existential type escapes out of its scope"
>   , what, text "Type:" <+> ppType m ty
>   ]

> errRecursiveType :: ModuleIdent -> Int -> Type -> Doc
> errRecursiveType m tv ty = errIncompatibleTypes m (TypeVariable tv) ty

> errMissingLabel :: ModuleIdent -> Ident -> Type -> Doc
> errMissingLabel m l rty = sep
>   [ text "Missing field for label" <+> ppIdent l
>   , text "in the record type" <+> ppType m rty
>   ]

> errIncompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
> errIncompatibleTypes m ty1 ty2 = sep
>   [ text "Types" <+> ppType m ty1
>   , nest 2 $ text "and" <+> ppType m ty2
>   , text "are incompatible"
>   ]

> errIncompatibleLabelTypes :: ModuleIdent -> Ident -> Type -> Type -> Doc
> errIncompatibleLabelTypes m l ty1 ty2 = sep
>   [ text "Labeled types" <+> ppIdent l <> text "::" <> ppType m ty1
>   , nest 10 $ text "and" <+> ppIdent l <> text "::" <> ppType m ty2
>   , text "are incompatible"
>   ]

> errEqualClassMethodAndFunctionNames :: ModuleIdent -> Ident -> Doc
> errEqualClassMethodAndFunctionNames _m f = 
>   text "Equal class method and top level function names: " <> ppIdent f

> -- TODO: position would be nice...
> errAmbiguousTypeVars :: Ident -> [Int] -> Message
> errAmbiguousTypeVars f _tvars 
>   = message (text "Ambiguous type variables in the context (function" 
>   <+> text (show f) <> text ")")

\end{verbatim}
The following functions implement pretty-printing for types.
\begin{verbatim}

> ppType :: ModuleIdent -> Type -> Doc
> ppType m = ppTypeExpr 0 . fromQualType m

> ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
> ppTypeScheme m (ForAll cx _ ty) = ppContext' m cx <+> text "=>" <+> ppType m ty

> ppContext' :: ModuleIdent -> BT.Context -> Doc
> ppContext' m cx = parens $ hsep $ 
>   punctuate comma (map (\(qid, ty) -> ppQIdent qid <+> ppType m ty) cx)

\end{verbatim}
After all type checking has been done, check at last, that there are 
no class methods with the name of one of the top level functions. 
\begin{verbatim}

> checkNoEqualClassMethodAndFunctionNames :: ValueEnv -> ClassEnv -> TCM ()
> checkNoEqualClassMethodAndFunctionNames vEnv cEnv = do
>   let classMethods = map fst3 $ getAllClassMethods cEnv
>   mapM_ searchClassMethod classMethods
>   where
>   searchClassMethod f 
>     = if not $ null $ lookupValue f vEnv -- TODO: use also qualLookupValue?
>       then do
>         m <- getModuleIdent
>         report $ message $ errEqualClassMethodAndFunctionNames m f
>       else return ()
>   fst3 (x, _, _) = x

\end{verbatim}