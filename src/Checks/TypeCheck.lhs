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

In the second run of the type checker, expanding types of type signatures  
(with expandType) must be disabled, because the type signatures are already
expanded. 
\begin{verbatim}

> module Checks.TypeCheck (typeCheck, bindTC, expandType) where

> import Control.Monad (liftM, liftM2, liftM3, replicateM, unless, when)
> import qualified Control.Monad.State as S (State, gets, modify, runState)
> import Data.List (nub, partition, sortBy)
> import qualified Data.Map as Map (Map, empty, insert, lookup)
> import Text.PrettyPrint
> -- import qualified Debug.Trace as Dbg
> import qualified Data.Set as Set
> import Data.Maybe

> import Curry.Base.Ident hiding (sep)
> import Curry.Base.Position
> import Curry.Syntax as ST
> import Curry.Syntax.Pretty

> import Base.CurryTypes (fromQualType, toConstrType, toConstrTypes)
> import Base.Expr
> import Base.Messages (Message, posMessage, internalError)
> import Base.SCC
> import Base.TopEnv
> import Base.Types as BT
> import Base.TypeSubst
> import Base.Subst (listToSubst, substToList)
> import Base.Utils (foldr2, findDouble, zip', zipWith', zipWith3', fromJust')

> import Env.TypeConstructor (TCEnv, TypeInfo (..), bindTypeInfo
>   , qualLookupTC)
> import Env.Value ( ValueEnv, ValueInfo (..), rebindFun
>   , bindGlobalInfo, bindLabel, lookupValue, qualLookupValue
>   , tryBindFun )
> import Env.ClassEnv (ClassEnv (..), Class (..)
>   , implies', implies, isValidCx, reduceContext, lookupTypeScheme)

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

The boolean parameter doContextRed0 specifies whether a context reduction 
should be exerted. This parameter is primarily for debugging, it is set
to True in the normal execution of the compiler. 
\begin{verbatim}

> typeCheck :: ModuleIdent -> TCEnv -> ValueEnv -> ClassEnv -> Bool -> Bool -> [Decl]
>           -> (TCEnv, ValueEnv, [Decl], [Message])
> typeCheck m tcEnv tyEnv cEnv doContextRed0 sndRun decls = execTCM check initState
>   where
>   pdecls = zip [0::Int ..] decls
>   check = do
>     checkTypeSynonyms m tds
>     bindTypes tds
>     bindConstrs
>     bindLabels
>     bindClassMethods cEnv
>     
>     -- assign each declaration a unique id
>     vdsN <- numberDecls vds
>     -- do the type check
>     (newDecls, _) <- tcDecls vdsN
>     -- correct the contexts of variables because of the context reduction
>     -- and apply the final type substitution to the type annotations
>     newDecls' <- correctVariableContexts newDecls
>     theta <- getTypeSubst
>     let newDecls'' = applyTypeSubst theta newDecls' 
>
>     -- cEnv' <- getClassEnv
>     -- vEnv <- getValueEnv
>     -- checkNoEqualClassMethodAndFunctionNames vEnv cEnv'
> 
>     -- checkForAmbiguousContexts vds
>
>     -- the second run should not produce any errors. If it does, we
>     -- did something wrong. 
>     secondRun0 <- isSecondRun 
>     errors0 <- getErrors
>     when (secondRun0 && not (null errors0)) $ 
>       internalError ("second type check failed: \n" ++ show (reverse errors0))
>     
>     -- restore the order of the declarations!
>     return (map snd $ sortBy sorter $ tds' ++ zip (map fst vds') newDecls'')
>   (tds', vds') = partition (isTypeDecl . snd) pdecls
>   tds = map snd tds'
>   vds = map snd vds'
>   sorter (n1, _) (n2, _) = compare n1 n2
>   initState = TcState m tcEnv tyEnv cEnv doContextRed0 idSubst emptySigEnv 
>     0 [] 0 Map.empty sndRun

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
>   , doContextRed :: Bool
>   , typeSubst   :: TypeSubst
>   , sigEnv      :: SigEnv
>   , nextId      :: Int         -- automatic counter
>   , errors      :: [Message]
>   , declCounter :: Int
>   , declGroups  :: Map.Map [Int] ([Decl], BT.Context)
>   , secondRun   :: Bool
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

> execTCM :: TCM [Decl] -> TcState -> (TCEnv, ValueEnv, [Decl], [Message])
> execTCM tcm s = let (decls, s') = S.runState tcm s
>                 in  ( tyConsEnv s'
>                     , typeSubst s' `subst` valueEnv s'
>                     , decls
>                     , reverse $ nub $ errors s'
>                     )

> -- hasError :: TCM Bool
> -- hasError = liftM (not . null) (S.gets errors)

> getErrors :: TCM [Message]
> getErrors = S.gets errors

> -- getOnlyNextId :: TCM Int
> -- getOnlyNextId = S.gets nextId

> -- resetNextId :: Int -> TCM ()
> -- resetNextId n = S.modify $ \s -> s { nextId = n}

> getDoContextRed :: TCM Bool
> getDoContextRed = S.gets doContextRed

> getNextDeclCounter :: TCM Int
> getNextDeclCounter = do
>   c <- S.gets declCounter
>   S.modify $ \ s -> s { declCounter = succ c }
>   return c

> -- | stores the declarations and their context by using the unique ids 
> -- of the declarations
> setDeclGroup :: [Decl] -> BT.Context -> TCM ()
> setDeclGroup ds cx = S.modify $
>   \s -> s { declGroups = Map.insert (map getUniqueId ds) (ds, cx) (declGroups s) }

> -- | loads the declarations and their context by using the unique ids of
> -- the declarations
> getDeclGroup :: [Decl] -> TCM (Maybe ([Decl], BT.Context))
> getDeclGroup ds = S.gets (Map.lookup (map getUniqueId ds) . declGroups)

> isSecondRun :: TCM Bool
> isSecondRun = S.gets secondRun

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
>     map getType $ expandMonoTypes m tcEnv (cleanTVars tvs evs) True (map noBContext tys)
> bindTC m tcEnv (NewtypeDecl _ tc tvs (NewConstrDecl _ evs c ty)) =
>   bindTypeInfo RenamingType m tc tvs (DataConstr c (length evs) [ty'])
>   where ty' = getType $ expandMonoType' m tcEnv (cleanTVars tvs evs) True (noBContext ty)
> bindTC m tcEnv (TypeDecl _ tc tvs ty) =
>   bindTypeInfo AliasType m tc tvs (getType $ expandMonoType' m tcEnv tvs True (noBContext ty))
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
The class methods are inserted into the value environment. Thus, they are 
treated just like any top level functions. Top level functions and 
class methods share the same namespace!
\begin{verbatim}

> {-
> -- |binds all class methods of /locally defined/ classes into the value
> -- environment  
> bindClassMethods :: ClassEnv -> TCM ()
> bindClassMethods cEnv = do
>   let allCls = allLocalClasses (theClasses cEnv)
>   mapM_ bindClass allCls  
> 
> -- |binds the class methods of the given class into the value environment, 
> -- just as if they were top level functions. 
> bindClass :: Class -> TCM ()
> bindClass cls = do
>   let tySchemes = typeSchemes cls
>   m <- getModuleIdent
>   vEnv <- getValueEnv
>   let vEnv' = foldr (\(id0, tsc) env -> 
>                       bindFun m id0 (arrowArity $ typeSchemeToType tsc) tsc env)
>                     vEnv
>                     tySchemes
>   modifyValueEnv $ const vEnv'
> -}
> 
> bindClassMethods :: ClassEnv -> TCM ()
> bindClassMethods (ClassEnv _ _ methodEnv _) = do 
>   vEnv <- getValueEnv
>   let classMethods0 = allBindings methodEnv
>       vEnv' = foldr bind vEnv classMethods0
>   modifyValueEnv $ const vEnv'
>   where
>   bind :: (QualIdent, Class) -> ValueEnv -> ValueEnv
>   bind (m, cls) = 
>     let tsc = fromJust $ lookupTypeScheme cls (unqualify m)
>         v = Value (qualifyLike (theClass cls) $ unqualify m) 
>                   (BT.arrowArity $ typeSchemeToType tsc) tsc
>     in qualImportTopEnv' (fromJust' "bindClassMethods" $ qidModule $ theClass cls) 
>          m v
>    
>     
 



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

> type PDecl = (Int, Decl)

> tcDecls :: [Decl] -> TCM ([Decl], BT.Context)
> tcDecls ds = do
>   m <- getModuleIdent
>   oldSig <- getSigEnv
>   modifySigEnv $ \ sigs -> foldr bindTypeSigs sigs ods
>   dsAndCxs <- mapM tcDeclGroup $ scc (bv . snd) (qfv m . snd) vds'
>   modifySigEnv (const oldSig)
>   let allDecls = ods' ++ concatMap fst dsAndCxs
>   -- restore the original order of the declarations again
>   return $ (map snd $ sortBy sorter allDecls, concatMap snd dsAndCxs)
>   where
>   -- record the order of the declarations by adding a position argument
>   pds = zip [0..] ds
>   (vds', ods') = partition (isValueDecl . snd) pds
>   ods = map snd ods'
>   sorter (n1, _) (n2, _) = compare n1 n2

> tcDeclGroup :: [PDecl] -> TCM ([PDecl], BT.Context)
> tcDeclGroup d@[(_, ForeignDecl _ _ _ f ty)] = tcForeign f ty >> return (d, BT.emptyContext)
> tcDeclGroup d@[(_, ExternalDecl      _ fs)] = mapM_ tcExternal fs >> return (d, BT.emptyContext)
> tcDeclGroup d@[(_, FreeDecl          _ vs)] = mapM_ tcFree     vs >> return (d, BT.emptyContext)
> tcDeclGroup pds                             = do
>   -- Strip the positions from the declarations, and add them later again. 
>   -- This can be done because the fix point iteration doesn't change
>   -- the order of the declarations
>   let ds   = map snd pds
>       poss = map fst pds
>   -- If declaration group is stored, take the results from the store. 
>   -- Else run (once!) the type checker for the specific declaration group and
>   -- store the results.
>   declGroup <- getDeclGroup ds
>   (ds', cx) <- case isNothing declGroup of
>     True -> do
>       (ds0, cx0) <- tcDeclGroup' ds 
>       setDeclGroup ds0 cx0
>       return (ds0, cx0)
>     False -> return (fromJust declGroup)
>   return (zip' poss ds', cx)

> tcDeclGroup' :: [Decl] -> TCM ([Decl], BT.Context) 
> tcDeclGroup' ds = do
>   tyEnv0 <- getValueEnv
>   ctysLhs <- mapM tcDeclLhs ds
>   dsAndCtysRhs <- mapM (tcDeclRhs tyEnv0) ds
>   -- get all contexts
>   let cxsLhs = map fst ctysLhs
>       ctysRhs = map snd dsAndCtysRhs
>       cxsRhs = map fst ctysRhs
>       cxs = zipWith (++) cxsLhs cxsRhs
>   sequence_ (zipWith3' unifyDecl ds ctysLhs ctysRhs)
>   theta <- getTypeSubst
>   let -- build the contexts of all declarations
>       -- nubbing contexts for avoiding exponential growth of the context lists
>       cxs' = map (nub . subst theta) cxs
>
>   let freeVars = fvEnv (subst theta tyEnv0)
>   
>   -- TODO: updateContexts needed (perhaps for pattern declarations)?
>   let newDs0 = {-zipWith updateContexts cxs' -}map fst dsAndCtysRhs
>   -- Propagate all contexts. 
>   newDs1 <- fpIter newDs0
>   -- Update contexts of function declarations with the contexts from the
>   -- type environment. This is very important, because we want that
>   -- the context reduction occuring at generalization yields exactly the
>   -- same results as the context reduction occuring in the dictionary 
>   -- transformation
>   newDs2 <- updateFuncContexts newDs1 
>   -- Establish the inferred types. 
>   mapM_ (genDecl freeVars theta) newDs1
>   -- do NOT return final contexts! 
>   -- TODO: return cxs or cxs' (or doesn't matter?)
>   return (newDs2, nonLocalContextElems freeVars $ concat cxs')

> -- |checks whether the given "ValueInfo" refers to an identifier from
> -- the given module
> valInMdl :: ModuleIdent -> ValueInfo -> Bool
> valInMdl m v = fromJust (qidModule $ origName v) == m

> -- |update the contexts (and only the contexts!) of the type signatures
> -- stored in the value environment 
> writeContexts :: [(BT.Context, Decl)] -> TCM ()
> writeContexts cs = mapM_ writeContext cs'
>   where
>   cs' = concatMap unpack cs
>   writeContext :: (BT.Context, Ident) -> TCM ()
>   writeContext (cx, v) = do
>     -- find the correct entry in the value environment
>     vEnv <- getValueEnv
>     let vs = lookupValue v vEnv
>     m <- getModuleIdent 
>     let vs' = filter (valInMdl m) vs
>         Value _ arity tysig = head vs'
>     when (length vs' /= 1) $ internalError "writeContexts" 
>     -- update the entry
>     let tysig' = tysig `constrainBy` cx
>     modifyValueEnv $ rebindFun m v arity tysig'
>   unpack (cx, FunctionDecl _ _ _ f _) = [(cx, f)]
>   unpack (cx, PatternDecl _ _ _ p _) = map (\d -> (cx, d)) (bv p)
>   unpack _ = internalError "unpack"

> {-
> -- |after the complete contexts have been determined, update the type annotations
> -- in the syntax tree with them
> updateContexts :: BT.Context -> Decl -> Decl
> updateContexts cx (FunctionDecl p (Just (_, ty)) id0 f es) 
>   = FunctionDecl p (Just (mirrorCx cx, ty)) id0 f es
> updateContexts cx (PatternDecl  p (Just (_, ty)) id0 pt rhs)
>   = PatternDecl  p (Just (mirrorCx cx, ty)) id0 pt rhs
> updateContexts _ _ = internalError "updateContexts"
> -}

> nonLocalContextElems :: Set.Set Int -> BT.Context -> BT.Context
> nonLocalContextElems fvs cx = filter (isNotLocal fvs) cx 

> -- | a context element is considered not local if it has type variables
> -- that are free variables of the type environment 
> isNotLocal :: Set.Set Int -> (QualIdent, Type) -> Bool
> isNotLocal fvs (_qid, ty) = any (`Set.member` fvs) (typeVars ty) 

> -- | updates the contexts in the function/pattern declarations with the
> -- contexts from the type environment
> updateFuncContexts :: [Decl] -> TCM [Decl]
> updateFuncContexts decls = mapM updateFuncContexts' decls
>   where
>   updateFuncContexts' :: Decl -> TCM Decl
>   updateFuncContexts' (FunctionDecl p (Just (_cx, ty)) n f eqs) = do
>     tyEnv <- getValueEnv
>     theta <- getTypeSubst
>     let cty = subst theta $ varType f tyEnv 
>     return $ FunctionDecl p (Just (mirrorFBCx $ getContext cty, ty)) n f eqs
>   updateFuncContexts' p@(PatternDecl _ _ _ _ _) = return p
>   updateFuncContexts' _ = internalError "updateFuncContexts'"

\end{verbatim}
The fix point iteration propagates all contexts in a declaration group until
the maximal necessary contexts for the functions are determined. 
\begin{verbatim}

> -- | This function does a fix point iteration, in the course of which  
> -- all contexts are propagated again and again until the maximal set of contexts
> -- is reached. 
> fpIter :: [Decl] -> TCM [Decl]
> fpIter ds = do
>   m <- getModuleIdent
>   vEnv <- getValueEnv
>   theta <- getTypeSubst
>   -- determine the very first context of a function declaration that
>   -- is given by its type signature. This is important, because we want
>   -- that the order of the elements in the inferred context is (roughly)
>   -- the same as that of the elements in the type signature.  
>   let maybeFs = map fromDecl ds 
>       ctys = map 
>         (fmap $ \v -> subst theta (funType m (qualify v) vEnv))
>         maybeFs
>   let firstContexts = map genContext ctys 
>   fpIter' ds firstContexts
>   where
>   fromDecl :: Decl -> Maybe Ident
>   fromDecl (FunctionDecl _ _ _ f _) = Just f
>   fromDecl (PatternDecl _ _ _ _ _) = Nothing 
>   fromDecl _ = internalError "fromDecl|fpIter"
>   genContext Nothing = []
>   genContext (Just tsc) = getContext tsc

> -- | Helper function for fix point iteration. The second argument is
> -- the list of contexts determined in the last run of the fix point iteration.  
> fpIter' :: [Decl] -> [[(QualIdent, Type)]] -> TCM [Decl]
> fpIter' ds oldCxs = do 
>   newDsAndCxs <- mapM fpDeclRhs ds
>   theta <- getTypeSubst
>   let cxs = map snd newDsAndCxs
>       cxs' = map (nub . subst theta) cxs
>       cxs'' = zipWith (++) oldCxs cxs'
>   case map Set.fromList oldCxs /= map Set.fromList cxs'' of
>     True -> do
>       writeContexts (zip cxs'' ds)
>       fpIter' (map fst newDsAndCxs) cxs''
>     False -> do
>       return ds 
>     

> fpDeclRhs :: Decl -> TCM (Decl, BT.Context)
> fpDeclRhs (FunctionDecl p (Just (cx0, ty0)) id0 f eqs) = do 
>   eqsAndCxs <- mapM fpEquation eqs
>   let cx' = concatMap snd eqsAndCxs
>   return (FunctionDecl p (Just (mirrorFBCx cx' ++ cx0, ty0)) id0 f (map fst eqsAndCxs), cx')
> fpDeclRhs (PatternDecl p (Just (cx0, ty0)) id0 t rhs) = do
>   (rhs', cx) <- fpRhs rhs
>   return (PatternDecl p (Just (mirrorFBCx cx ++ cx0, ty0)) id0 t rhs', cx) 
> fpDeclRhs _ = internalError "fpDeclRhs"

> fpEquation :: Equation -> TCM (Equation, BT.Context)
> fpEquation (Equation p lhs rhs) = do
>   (rhs', cx) <- fpRhs rhs
>   return (Equation p lhs rhs', cx)

> fpRhs :: Rhs -> TCM (Rhs, BT.Context)
> fpRhs (SimpleRhs p e ds) = do
>   (ds', cxDs) <- tcDecls ds
>   (e', cxE) <- fpExpr e
>   return (SimpleRhs p e' ds', cxE ++ cxDs)
> fpRhs (GuardedRhs es ds) = do
>   (ds', cxDs) <- tcDecls ds
>   (es', cxEs) <- fpCondExprs es
>   return (GuardedRhs es' ds', cxEs ++ cxDs)

> fpCondExprs :: [CondExpr] -> TCM ([CondExpr], BT.Context)
> fpCondExprs ces = do
>   cesWithCxs <- mapM fpCondExpr ces
>   return (map fst cesWithCxs, concatMap snd cesWithCxs)

> fpCondExpr :: CondExpr -> TCM (CondExpr, BT.Context)
> fpCondExpr (CondExpr p g e) = do
>   (e', cxE) <- fpExpr e
>   (g', cxG) <- fpExpr g
>   return (CondExpr p g' e', cxE ++ cxG)

> fpExpr :: Expression -> TCM (Expression, BT.Context)
> fpExpr l@(Literal _) = return (l, BT.emptyContext)
> fpExpr (Variable (Just (_cx0, ty0)) v) = do
>   m <- getModuleIdent
>   theta <- getTypeSubst
>   sigs <- getSigEnv
>   tsc <- getValueEnv >>= \vEnv -> return (funType m v vEnv)
>   let tySig = qualLookupTypeSig m v sigs
>   case isJust tySig of
>     False -> do
>       let mapping = buildTypeVarsMapping (typeSchemeToType tsc) (mirrorBFTy ty0)
>           cx' = subst mapping (getContext tsc)
>       return (Variable (Just (mirrorFBCx cx', ty0)) v, cx')
>     True -> do
>       let mapping = buildTypeVarsMapping (subst theta $ typeSchemeToType tsc) (mirrorBFTy ty0)
>           cx' = subst mapping (subst theta $ getContext tsc)  
>       return (Variable (Just (mirrorFBCx cx', ty0)) v, cx')
> fpExpr (Variable Nothing v) = do
>   internalError ("fpExpr Nothing: " ++ show v) 
> fpExpr c@(Constructor _) = return (c, BT.emptyContext)
> fpExpr (Paren e) = do 
>   (e', cx) <- fpExpr e
>   return (Paren e', cx)
> fpExpr (Typed cty@(Just (cx1, _ty1)) e cx0 ty) = do
>   (e', cx) <- fpExpr e
>   return (Typed cty e' cx0 ty, cx ++ mirrorBFCx cx1)
> fpExpr (Typed Nothing _ _ _) = internalError "fpExpr"
> fpExpr (Tuple sref es) = do
>   esAndCxs <- mapM fpExpr es
>   return (Tuple sref (map fst esAndCxs), concatMap snd esAndCxs)
> fpExpr (List sref es) = do
>   esAndCxs <- mapM fpExpr es
>   return (List sref (map fst esAndCxs), concatMap snd esAndCxs)
> fpExpr (ListCompr sref e ss) = do
>   (e', cx) <- fpExpr e
>   ssAndCxs <- mapM fpStmt ss
>   return (ListCompr sref e' (map fst ssAndCxs), cx ++ concatMap snd ssAndCxs)
> fpExpr (EnumFrom e1) = do
>   (e1', cx1) <- fpExpr e1
>   return (EnumFrom e1', cx1)
> fpExpr (EnumFromThen e1 e2) = do
>   (e1', cx1) <- fpExpr e1
>   (e2', cx2) <- fpExpr e2
>   return (EnumFromThen e1' e2', cx1 ++ cx2)
> fpExpr (EnumFromTo e1 e2) = do
>   (e1', cx1) <- fpExpr e1
>   (e2', cx2) <- fpExpr e2
>   return (EnumFromTo e1' e2', cx1 ++ cx2)
> fpExpr (EnumFromThenTo e1 e2 e3) = do
>   (e1', cx1) <- fpExpr e1
>   (e2', cx2) <- fpExpr e2
>   (e3', cx3) <- fpExpr e3
>   return (EnumFromThenTo e1' e2' e3', cx1 ++ cx2 ++ cx3)
> fpExpr (UnaryMinus id0 e) = do
>   (e', cx) <- fpExpr e
>   return (UnaryMinus id0 e', cx)
> fpExpr (Apply e1 e2) = do
>   (e1', cx1) <- fpExpr e1
>   (e2', cx2) <- fpExpr e2
>   -- theta <- getTypeSubst
>   return (Apply e1' e2', {-subst theta -}(cx1 ++ cx2))
> fpExpr (InfixApply e1 op e2) = do
>   (e1', cx1) <- fpExpr e1
>   (_op', cxO) <- fpExpr (infixOp op)
>   (e2', cx2) <- fpExpr e2
>   -- theta <- getTypeSubst
>   return (InfixApply e1' op e2', {-subst theta -}(cx1 ++ cxO ++ cx2))
> fpExpr (LeftSection e1 op) = do
>   (e1', cx1) <- fpExpr e1
>   (_op', cxO) <- fpExpr (infixOp op)
>   -- theta <- getTypeSubst
>   return (LeftSection e1' op, {-subst theta -}(cx1 ++ cxO))
> fpExpr (RightSection op e1) = do
>   (e1', cx1) <- fpExpr e1
>   (_op', cxO) <- fpExpr (infixOp op)
>   -- theta <- getTypeSubst
>   return (RightSection op e1', {-subst theta -}(cx1 ++ cxO))
> fpExpr (Lambda sref ps e) = do
>   (e', cx) <- fpExpr e
>   return (Lambda sref ps e', cx)
> fpExpr (Let ds e) = do
>   (ds', cxDs) <- tcDecls ds
>   (e', cx) <- fpExpr e
>   return (Let ds' e', cx ++ cxDs)
> fpExpr (Do ss e) = do
>   ssAndCxs <- mapM fpStmt ss
>   (e', cx) <- fpExpr e
>   return (Do (map fst ssAndCxs) e', cx ++ concatMap snd ssAndCxs)
> fpExpr (IfThenElse sref e1 e2 e3) = do
>   (e1', cx1) <- fpExpr e1
>   (e2', cx2) <- fpExpr e2
>   (e3', cx3) <- fpExpr e3
>   return (IfThenElse sref e1' e2' e3', cx1 ++ cx2 ++ cx3)
> fpExpr (Case sref ct e alts) = do
>   (e', cxE) <- fpExpr e
>   altsWithCxs <- mapM fpAlt alts
>   return (Case sref ct e' (map fst altsWithCxs), cxE ++ concatMap snd altsWithCxs)
> fpExpr (RecordConstr fs) = do
>   fsWithCxs <- mapM fpField fs
>   return (RecordConstr (map fst fsWithCxs), concatMap snd fsWithCxs)
> fpExpr (RecordSelection e i) = do
>   (e', cxE) <- fpExpr e
>   return (RecordSelection e' i, cxE)
> fpExpr (RecordUpdate fs e) = do
>   fsWithCxs <- mapM fpField fs
>   (e', cxE) <- fpExpr e
>   return (RecordUpdate (map fst fsWithCxs) e', concatMap snd fsWithCxs ++ cxE)

> fpStmt :: Statement -> TCM (Statement, BT.Context)
> fpStmt (StmtExpr sref e) = do
>   (e', cxE) <- fpExpr e
>   return (StmtExpr sref e', cxE)
> fpStmt (StmtDecl ds) = do
>   (ds', cx') <- tcDecls ds
>   return (StmtDecl ds', cx')
> fpStmt (StmtBind sref p e) = do
>   (e', cxE) <- fpExpr e
>   return (StmtBind sref p e', cxE)

> fpAlt :: Alt -> TCM (Alt, BT.Context)
> fpAlt (Alt p pt rhs) = do
>   (rhs', cx) <- fpRhs rhs
>   return (Alt p pt rhs', cx)

> fpField :: Field Expression -> TCM (Field Expression, BT.Context)
> fpField (Field p i e) = do
>   (e', cxE) <- fpExpr e
>   return (Field p i e', cxE)


> -- | This function is called after all type checking has been done. Because
> -- context reduction in a declaration group is always done at the very end 
> -- of generalization, the contexts in the type annotations of variables
> -- have to be updated so that they reflect the changes introduced by the
> -- context reduction.  
> correctVariableContexts :: [Decl] -> TCM [Decl]
> correctVariableContexts ds = mapM cvcDecl ds

> cvcDecl :: Decl -> TCM Decl
> cvcDecl (FunctionDecl p cty n id0 eqs) = FunctionDecl p cty n id0 `liftM` mapM cvcEqu eqs
> cvcDecl (PatternDecl p cty n pt rhs) = PatternDecl p cty n pt `liftM` cvcRhs rhs
> cvcDecl x = return x

> cvcEqu :: Equation -> TCM Equation
> cvcEqu (Equation p lhs rhs) = Equation p lhs `liftM` cvcRhs rhs

> cvcRhs :: Rhs -> TCM Rhs
> cvcRhs (SimpleRhs p e ds) = liftM2 (SimpleRhs p) (cvcExpr e) (mapM cvcDecl ds)
> cvcRhs (GuardedRhs ces ds) = liftM2 GuardedRhs (mapM cvcCondExpr ces) (mapM cvcDecl ds)

> cvcExpr :: Expression -> TCM Expression
> cvcExpr l@(Literal _) = return l
> cvcExpr (Variable (Just (_cx0, ty0)) v) = do
>   tyEnv <- getValueEnv 
>   m <- getModuleIdent
>   theta <- getTypeSubst
>   let ForAll cxInf _ tyInf = funType m v tyEnv
>   let s = either (internalError . show) id (unifyTypes m tyInf (subst theta $ mirrorBFTy ty0))
>   return $ Variable (Just (mirrorFBCx $ subst s cxInf, ty0)) v
> cvcExpr (Variable Nothing v) = internalError ("no type info for Variable " ++ show v) 
> cvcExpr c@(Constructor _) = return c
> cvcExpr (Paren e) = Paren `liftM` cvcExpr e
> cvcExpr (Typed cty e cx ty) = liftM3 (Typed cty) (cvcExpr e) (return cx) (return ty)
> cvcExpr (Tuple sref es) = Tuple sref `liftM` mapM cvcExpr es
> cvcExpr (List sref es) = List sref `liftM` mapM cvcExpr es
> cvcExpr (ListCompr sref e ss) = liftM2 (ListCompr sref) (cvcExpr e) (mapM cvcStmt ss)
> cvcExpr (EnumFrom e1) = EnumFrom `liftM` (cvcExpr e1)
> cvcExpr (EnumFromThen e1 e2) = liftM2 EnumFromThen (cvcExpr e1) (cvcExpr e2)
> cvcExpr (EnumFromTo e1 e2) = liftM2 EnumFromTo (cvcExpr e1) (cvcExpr e2)
> cvcExpr (EnumFromThenTo e1 e2 e3) = liftM3 EnumFromThenTo (cvcExpr e1) (cvcExpr e2) (cvcExpr e3)
> cvcExpr (UnaryMinus i e) = UnaryMinus i `liftM` cvcExpr e
> cvcExpr (Apply e1 e2) = liftM2 Apply (cvcExpr e1) (cvcExpr e2)
> cvcExpr (InfixApply e1 op e2) = liftM3 InfixApply (cvcExpr e1) (cvcInfixOp op) (cvcExpr e2)
> cvcExpr (LeftSection e op) = liftM2 LeftSection (cvcExpr e) (cvcInfixOp op)
> cvcExpr (RightSection op e) = liftM2 RightSection (cvcInfixOp op) (cvcExpr e)
> cvcExpr (Lambda sref ps e) = Lambda sref ps `liftM` (cvcExpr e)
> cvcExpr (Let ds e) = liftM2 Let (mapM cvcDecl ds) (cvcExpr e)
> cvcExpr (Do ss e) = liftM2 Do (mapM cvcStmt ss) (cvcExpr e)
> cvcExpr (IfThenElse sref e1 e2 e3) = liftM3 (IfThenElse sref) (cvcExpr e1) (cvcExpr e2) (cvcExpr e3)
> cvcExpr (Case sref ct e alts) = liftM2 (Case sref ct) (cvcExpr e) (mapM cvcAlt alts)
> cvcExpr (RecordConstr fs) = RecordConstr `liftM` mapM cvcField fs
> cvcExpr (RecordSelection e i) = flip RecordSelection i `liftM` cvcExpr e
> cvcExpr (RecordUpdate fs e) = liftM2 RecordUpdate (mapM cvcField fs) (cvcExpr e)

> cvcInfixOp :: InfixOp -> TCM InfixOp
> cvcInfixOp (InfixOp (Just (_cx0, ty0)) qid) = do
>   tyEnv <- getValueEnv 
>   m <- getModuleIdent
>   theta <- getTypeSubst
>   let ForAll cxInf _ tyInf = funType m qid tyEnv
>   let s = either (internalError . show) id (unifyTypes m tyInf (subst theta $ mirrorBFTy ty0))
>   return $ InfixOp (Just (mirrorFBCx $ subst s cxInf, ty0)) qid
> cvcInfixOp (InfixOp Nothing _) = internalError "cvcInfixOp"
> cvcInfixOp ic@(InfixConstr _) = return ic

> cvcCondExpr :: CondExpr -> TCM CondExpr
> cvcCondExpr (CondExpr p e1 e2) = liftM2 (CondExpr p) (cvcExpr e1) (cvcExpr e2)

> cvcStmt :: Statement -> TCM Statement
> cvcStmt (StmtExpr sref e) = StmtExpr sref `liftM` cvcExpr e
> cvcStmt (StmtDecl ds) = StmtDecl `liftM` mapM cvcDecl ds
> cvcStmt (StmtBind sref p e) = StmtBind sref p `liftM` cvcExpr e

> cvcAlt :: Alt -> TCM Alt
> cvcAlt (Alt p pt rhs) = Alt p pt `liftM` cvcRhs rhs

> cvcField :: Field Expression -> TCM (Field Expression)
> cvcField (Field p i e) = Field p i `liftM` cvcExpr e  

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
>   sndRun <- isSecondRun
>   tySc@(ForAll _cx _ ty') <- expandPolyType (not sndRun) (ST.emptyContext, ty)
>   modifyValueEnv $ bindFunOnce m f (arrowArity ty') tySc

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
>   sndRun <- isSecondRun
>   ty <- case lookupTypeSig v sigs of
>     Nothing -> freshTypeVar
>     Just t  -> do
>       ForAll _cx n ty' <- expandPolyType (not sndRun) t
>       unless (n == 0) $ report $ errPolymorphicFreeVar v
>       return ty'
>   modifyValueEnv $ bindFunOnce m v (arrowArity ty) $ monoType ty

> tcDeclLhs :: Decl -> TCM ConstrType
> tcDeclLhs (FunctionDecl _ _ _ f _) = tcFunDecl f
> tcDeclLhs (PatternDecl  p _ _ t _) = tcPattern p t
> tcDeclLhs _ = internalError "TypeCheck.tcDeclLhs: no pattern match"

> tcFunDecl :: Ident -> TCM ConstrType
> tcFunDecl v = do
>   sigs <- getSigEnv
>   m <- getModuleIdent
>   sndRun <- isSecondRun
>   (cx, ty) <- case lookupTypeSig v sigs of
>     Nothing -> freshConstrTypeVar
>     Just t  -> expandPolyType (not sndRun) t >>= inst
>   modifyValueEnv $ bindFunOnce m v (arrowArity ty) (monoType' (cx, ty))
>   return (cx, ty)

> tcDeclRhs :: ValueEnv -> Decl -> TCM (Decl, ConstrType)
> tcDeclRhs tyEnv0 (FunctionDecl p0 _ id0 f (eq:eqs)) = do
>   (eq', (cx0, ty0)) <- tcEquation tyEnv0 eq
>   (eqs', (cxs, ty)) <- tcEqns ty0 [] eqs [eq']
>   let cty = (cx0 ++ cxs, ty)
>   return (FunctionDecl p0 (Just $ mirrorFBCT cty) id0 f eqs', cty)
>   where tcEqns :: Type -> BT.Context -> [Equation] -> [Equation] -> TCM ([Equation], ConstrType)
>         tcEqns ty cxs [] newEqs = return (reverse newEqs, (cxs, ty))
>         tcEqns ty cxs (eq1@(Equation p _ _):eqs1) newEqs = do
>           (eq1', cty'@(cx', _ty')) <- tcEquation tyEnv0 eq1
>           unify p "equation" (ppDecl (FunctionDecl p Nothing id0 f [eq1])) (noContext ty) cty'
>           tcEqns ty (cx' ++ cxs) eqs1 (eq1':newEqs)
> tcDeclRhs tyEnv0 (PatternDecl p _ id0 t rhs) = do
>   (rhs', cty) <- tcRhs tyEnv0 rhs
>   return (PatternDecl p (Just $ mirrorFBCT cty) id0 t rhs', cty)
> tcDeclRhs _ _ = internalError "TypeCheck.tcDeclRhs: no pattern match"

> unifyDecl :: Decl -> ConstrType -> ConstrType -> TCM ()
> unifyDecl (FunctionDecl p _ _ f _) =
>   unify p "function binding" (text "Function:" <+> ppIdent f)
> unifyDecl (PatternDecl  p _ _ t _) =
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

> genDecl :: Set.Set Int -> TypeSubst -> Decl -> TCM ()
> genDecl lvs theta (FunctionDecl _ _ _ f (Equation _ lhs _ : _)) = 
>   genVar True lvs theta arity f
>   where arity = Just $ length $ snd $ flatLhs lhs
> genDecl lvs theta (PatternDecl  _ _ _ t _) = 
>   mapM_ (genVar False lvs theta Nothing) (bv t)
> genDecl _ _ _ = internalError "TypeCheck.genDecl: no pattern match"

> genVar :: Bool -> Set.Set Int -> TypeSubst -> Maybe Int 
>        -> Ident -> TCM ()
> genVar poly lvs theta ma v = do
>   sigs <- getSigEnv
>   m <- getModuleIdent
>   tyEnv <- getValueEnv
>   cEnv <- getClassEnv
>   doContextRed0 <- getDoContextRed
>   let sigma0 = genType poly $ subst theta $ varType v tyEnv
>       arity  = fromMaybe (varArity v tyEnv) ma
>       -- apply context reduction
>       generalizedContext = getContext sigma0
>       finalContext = (if doContextRed0 then reduceContext cEnv else id)
>         generalizedContext
>       sigma = sigma0 `constrainBy` finalContext
>       context = finalContext
>   -- check that the context is valid
>   let invalidCx = isValidCx cEnv context
>   unless (null invalidCx) $ report $ errNoInstance (idPosition v) m invalidCx
>   -- check for ambiguous context elements
>   let tyVars = typeVars (typeSchemeToType sigma)
>       ambigCxElems = filter (isAmbiguous tyVars lvs) context 
>   unless (null ambigCxElems) $ case lookupTypeSig v sigs of 
>     Nothing -> report $ errAmbiguousContextElems (idPosition v) m v ambigCxElems
>     Just tySig -> do
>       -- check whether there are ambiguous type variables in the 
>       -- unexpanded (!) type signature. TODO: Actually we could do without this
>       -- test because we know that type signatures are unambiguous (as this
>       -- is checked earlier) 
>       tySig' <- expandPolyType False tySig
>       let tyVars' = typeVars (typeSchemeToType tySig')
>           ambigCxElems' = filter (isAmbiguous tyVars' Set.empty) (getContext tySig')
>       unless (null ambigCxElems') $ report $ 
>         errAmbiguousContextElems (idPosition v) m v ambigCxElems'
>   sndRun <- isSecondRun
>   case lookupTypeSig v sigs of
>     Nothing    -> modifyValueEnv $ rebindFun m v arity sigma
>     Just sigTy -> do
>       sigma' <- expandPolyType (not sndRun) sigTy
>       case (eqTyScheme sigma sigma') of 
>         False -> report  $ errTypeSigTooGeneral (idPosition v) m what sigTy sigma
>         True -> do
>           -- check that the given context implies the inferred
>           let mapping = buildTypeVarsMapping (typeSchemeToType sigma') (typeSchemeToType sigma)
>               context' = subst mapping $ getContext sigma' 
>           unless (implies' cEnv context' context)
>             $ report $ errContextImplication (idPosition v) m context' context
>               (filter (not . implies cEnv context') context)  
>               v
>       modifyValueEnv $ rebindFun m v arity sigma
>   where
>   what = text (if poly then "Function:" else "Variable:") <+> ppIdent v
>   genType poly' (ForAll cx0 n ty)
>     | n > 0 = internalError $ "TypeCheck.genVar: " ++ showLine (idPosition v) ++ show v ++ " :: " ++ show ty
>     | poly' = gen lvs (cx0, ty)
>     | otherwise = monoType' (cx0, ty)
>   eqTyScheme (ForAll _cx1 _ t1) (ForAll _cx2 _ t2) = equTypes t1 t2

> -- | Returns whether the given context element is ambiguous.
> -- A context element in the type signature C => T is exactly then ambiguous 
> -- if it contains a type variable that does not appear in T and which 
> -- is not free in the current type environment (definition from 
> -- "Implementing Haskell Type Classes", K. Hammond and S. Blott)
> isAmbiguous :: [Int]             -- ^ the type variables from T 
>             -> Set.Set Int       -- ^ the free type vars in the current type environment
>             -> (QualIdent, Type) -- ^ the context elem to be examined
>             -> Bool
> isAmbiguous tyVarsType freeVars (_qid, ty0) = 
>   let tyVarsCxElem = typeVars ty0
>   in any (\ty -> ty `notElem` tyVarsType && not (ty `Set.member` freeVars)) tyVarsCxElem

> -- | builds a mapping from type variables in the left type to the type variables
> -- in the right type. Assumes that the types are alpha equivalent. 
> buildTypeVarsMapping :: Type -> Type -> TypeSubst
> buildTypeVarsMapping t1 t2 = 
>   if bijective theMapping
>   then listToSubst $ map (\(n, n2) -> (n, TypeVariable n2)) $ theMapping
>   else internalError ("mapping not bijective " ++ show theMapping)
>   where
>   theMapping :: [(Int, Int)]
>   theMapping = nub $ buildTypeVarsMapping' t1 t2
>   bijective :: [(Int, Int)] -> Bool
>   bijective m = injective m && injective (map (\(x, y) -> (y, x)) m)
>   injective :: [(Int, Int)] -> Bool
>   injective m = isNothing $ findDouble (map snd m) 

> buildTypeVarsMapping' :: Type -> Type -> [(Int, Int)]
> buildTypeVarsMapping' (TypeVariable n1) (TypeVariable n2) = [(n1, n2)]
> buildTypeVarsMapping' (TypeConstructor _ ts1) (TypeConstructor _ ts2)
>   = concat $ zipWith' buildTypeVarsMapping' ts1 ts2
> buildTypeVarsMapping' (TypeArrow t11 t12) (TypeArrow t21 t22)
>   = buildTypeVarsMapping' t11 t21 ++ buildTypeVarsMapping' t12 t22
> buildTypeVarsMapping' (TypeConstrained _ _) (TypeConstrained _ _) = [] 
> buildTypeVarsMapping' (TypeSkolem _) (TypeSkolem _) = []
> buildTypeVarsMapping' (TypeRecord ids1 (Just i1)) (TypeRecord ids2 (Just i2))
>   = concat (zipWith' buildTypeVarsMapping' (map snd ids1) (map snd ids2)) 
>     ++ [(i1, i2)]
> buildTypeVarsMapping' (TypeRecord ids1 Nothing) (TypeRecord ids2 Nothing)
>   = concat $ zipWith' buildTypeVarsMapping' (map snd ids1) (map snd ids2) 
> buildTypeVarsMapping' t1 t2 = 
>   internalError ("types do not match in buildTypeVarsMapping\n" ++ show t1 
>     ++ "\n" ++ show t2)

> tcEquation :: ValueEnv -> Equation -> TCM (Equation, ConstrType)
> tcEquation tyEnv0 (Equation p lhs rhs) = do
>   tys <- mapM (tcPattern p) ts
>   (rhs', (cx, ty)) <- tcRhs tyEnv0 rhs
>   let cxs = concat $ map fst tys ++ [cx] 
>   cty <- checkSkolems p (text "Function: " <+> ppIdent f) tyEnv0
>                         (cxs, foldr TypeArrow ty (map getType tys))
>   return (Equation p lhs rhs', cty)
>   where (f, ts) = flatLhs lhs

> tcLiteral :: Literal -> TCM ConstrType
> tcLiteral (Char   _ _) = return (BT.emptyContext, charType)
> tcLiteral (Int    v _)  = do --return intType
>   m  <- getModuleIdent
>   ty <- freshConstrained [intType, floatType]
>   modifyValueEnv $ bindFunOnce m v (arrowArity ty) $ monoType ty
>   return (BT.emptyContext, ty)
> tcLiteral (Float  _ _) = return (BT.emptyContext, floatType)
> tcLiteral (String _ _) = return (BT.emptyContext, stringType)

> tcPattern :: Position -> Pattern -> TCM ConstrType
> tcPattern _ (LiteralPattern    l) = tcLiteral l
> tcPattern _ (NegativePattern _ l) = tcLiteral l
> tcPattern _ (VariablePattern   v) = do
>   sigs <- getSigEnv
>   sndRun <- isSecondRun
>   (cx, ty) <- case lookupTypeSig v sigs of
>     Nothing -> freshConstrTypeVar
>     Just t  -> expandPolyType (not sndRun) t >>= inst
>   tyEnv <- getValueEnv
>   m  <- getModuleIdent
>   maybe (modifyValueEnv (bindFunOnce m v (arrowArity ty) (monoType' (cx, ty))) >> return (cx, ty))
>         (\ (ForAll cx0 _ t) -> return (cx0, t))
>         (sureVarType v tyEnv)
> tcPattern p t@(ConstructorPattern c ts) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- skol $ constrType m c tyEnv
>   unifyArgs (ppPattern 0 t) ts ty []
>   where unifyArgs _   []       ty cx = return (cx, ty)
>         unifyArgs doc (t1:ts1) (TypeArrow ty1 ty2) cx = do
>           cty1@(cx1, _) <- tcPattern p t1
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty1) cty1
>           unifyArgs doc ts1 ty2 (cx ++ cx1)
>         unifyArgs _ _ _ _ = internalError "TypeCheck.tcPattern"
> tcPattern p t@(InfixPattern t1 op t2) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- skol (constrType m op tyEnv)
>   unifyArgs (ppPattern 0 t) [t1,t2] ty []
>   where unifyArgs _ [] ty cx = return (cx, ty)
>         unifyArgs doc (t':ts') (TypeArrow ty1 ty2) cx = do
>           cty1@(cx1, _) <- tcPattern p t' 
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t')
>                 (noContext ty1) cty1
>           unifyArgs doc ts' ty2 (cx ++ cx1)
>         unifyArgs _ _ _ _ = internalError "TypeCheck.tcPattern"
> tcPattern p (ParenPattern t) = tcPattern p t
> tcPattern p (TuplePattern _ ts)
>  | null ts   = return $ noContext unitType
>  | otherwise = do
>      ctys <- mapM (tcPattern p) ts
>      let ty = tupleType $ (map snd ctys)
>      return (concatMap fst ctys, ty) 
> tcPattern p t@(ListPattern _ ts) =
>   freshTypeVar >>= flip (tcElems [] (ppPattern 0 t)) ts
>   where tcElems cx _ ty [] = return (cx, listType ty)
>         tcElems cx doc ty (t1:ts1) = do
>           cty1@(cx1, _) <- tcPattern p t1
>           unify p "pattern" (doc $-$ text "Term:" <+> ppPattern 0 t1)
>                 (noContext ty) cty1
>           tcElems (cx ++ cx1) doc ty ts1
> tcPattern p t@(AsPattern v t') = do
>   cty1@(cx1, ty1) <- tcPattern p (VariablePattern v)
>   cty2@(cx2, _  ) <- tcPattern p t'
>   unify p "pattern" (ppPattern 0 t) cty1 cty2
>   return (cx1 ++ cx2, ty1)
> tcPattern p (LazyPattern _ t) = tcPattern p t
> tcPattern p t@(FunctionPattern f ts) = do
>   m     <- getModuleIdent
>   tyEnv <- getValueEnv
>   ty <- inst (funType m f tyEnv) --skol (constrType m c tyEnv)
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
>   sndRun <- isSecondRun
>   cty@(cx, ty) <- case lookupTypeSig v sigs of
>     Nothing -> freshConstrTypeVar
>     Just t  -> expandPolyType (not sndRun) t >>= inst
>   tyEnv <- getValueEnv
>   maybe (modifyValueEnv (bindFunOnce m v (arrowArity ty) (monoType' cty)) >> return cty)
>         (\ (ForAll cx0 _ t) -> return (cx0, t))
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
>     ty <- inst (funType m f tyEnv) --skol (constrType m c tyEnv)
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

> tcRhs ::ValueEnv -> Rhs -> TCM (Rhs, ConstrType)
> tcRhs tyEnv0 (SimpleRhs p e ds) = do
>   (ds', cxs) <- tcDecls ds
>   (e', (cx, ty)) <- tcExpr p e
>   cty <- checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cx ++ cxs, ty)
>   return (SimpleRhs p e' ds', cty)
> tcRhs tyEnv0 (GuardedRhs es ds) = do
>   (ds', cxs) <- tcDecls ds
>   (es', (cxs', ty)) <- tcCondExprs tyEnv0 es
>   return (GuardedRhs es' ds', (cxs' ++ cxs, ty))

> tcCondExprs :: ValueEnv -> [CondExpr] -> TCM ([CondExpr], ConstrType)
> tcCondExprs tyEnv0 es = do
>   gty <- if length es > 1 then return $ noContext boolType
>                           else liftM noContext $ freshConstrained [successType,boolType]
>   cty <- freshConstrTypeVar
>   tcCondExprs' gty cty [] es []
>   where tcCondExprs' :: ConstrType -> ConstrType -> BT.Context -> [CondExpr] 
>                      -> [CondExpr] -> TCM ([CondExpr], ConstrType)
>         tcCondExprs' _ (_, ty) cx [] newCs = return (reverse newCs, (cx, ty))
>         tcCondExprs' gty cty cx (e1:es1) newCs = do
>           (ce', cx') <- tcCondExpr gty cty e1
>           tcCondExprs' gty cty (cx ++ cx') es1 (ce':newCs)
>         tcCondExpr :: ConstrType -> ConstrType -> CondExpr -> TCM (CondExpr, BT.Context)
>         tcCondExpr gty cty@(_cx, _) (CondExpr p g e) = do
>           (g', cty1@(cx1, _)) <- tcExpr p g
>           unify p "guard" (ppExpr 0 g) gty cty1
>           (e', cty2)          <- tcExpr p e
>           cty3@(cx3, _) <- checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 cty2
>           unify p "guarded expression" (ppExpr 0 e) cty cty3
>           return (CondExpr p g' e', cx1 ++ cx3)

> tcExpr :: Position -> Expression -> TCM (Expression, ConstrType)
> tcExpr _ e@(Literal     l) = do
>   cty <- tcLiteral l
>   return (e, cty)
> tcExpr _ (Variable  _ v)
>     -- anonymous free variable
>   | isAnonId v' = do
>       m <- getModuleIdent
>       ty <- freshTypeVar
>       modifyValueEnv $ bindFunOnce m v' (arrowArity ty) $ monoType ty
>       return $ (Variable (Just $ mirrorFBCT $ noContext ty) v, noContext ty)
>   | otherwise    = do
>       sigs <- getSigEnv
>       m <- getModuleIdent
>       sndRun <- isSecondRun
>       case qualLookupTypeSig m v sigs of
>         Just cty -> do
>           -- load the inferred type together with the contexts
>           (icx, ity) <- getValueEnv >>= inst . funType m v
>           -- retrieve the type from the type signature...
>           (cx0, ty0) <- expandPolyType (not sndRun) cty >>= inst
>           -- ... and construct a mapping, so that the type variables in the 
>           -- inferred contexts match the type variables in the type
>           -- constructed from the type signature
>           let mapping = buildTypeVarsMapping ity ty0
>               cty' = (cx0 ++ subst mapping icx, ty0)
>           return (Variable (Just $ mirrorFBCT cty') v, cty')
>         Nothing -> do
>           cty <- getValueEnv >>= inst . funType m v
>           return (Variable (Just $ mirrorFBCT cty) v, cty)
>   where v' = unqualify v
> tcExpr _ e@(Constructor c) = do
>  m <- getModuleIdent
>  cty <- getValueEnv >>= instExist . constrType m c
>  return (e, cty)
> tcExpr p (Typed _ e cx sig) = do
>   m <- getModuleIdent
>   tyEnv0 <- getValueEnv
>   (e', cty@(cxInf, tyInf)) <- tcExpr p e
>   sigma' <- expandPolyType True (cx, sig')
>   inst sigma' >>= flip (unify p "explicitly typed expression" (ppExpr 0 e)) cty
>   theta <- getTypeSubst
>   let (sigma, s) = genS (fvEnv (subst theta tyEnv0)) 
>                         (subst theta (cxInf, tyInf)) 
>       -- this is safe here because "gen" uses only substitutions of the 
>       -- form (Int, TypeVariable Int)
>       s' = reverseTySubst s
>   sndRun <- isSecondRun
>   -- issue errors only in the first run of the type check
>   unless (eqTypes sigma sigma') $ when (not sndRun) $ 
>     (report $ errTypeSigTooGeneral p m (text "Expression:" <+> ppExpr 0 e) (cx, sig') sigma)
>   cEnv <- getClassEnv
>   -- test context implication
>   let cxGiven = getContext sigma'
>       cxInf' = getContext sigma
>   unless (implies' cEnv cxGiven cxInf') $ report $
>     errContextImplication p m cxGiven cxInf'
>     (filter (not . implies cEnv cxGiven) cxInf')
>     (mkIdent "explicitely typed expression")
>   -- Merge contexts. Note that the context cxGiven originates from the 
>   -- type signature, not from the inferred type. Thus the type variables 
>   -- in cxGiven don't refer to the type variables in the inferred type.  
>   -- Because of this we have to "substitute" the type variables "back", so
>   -- that they correctly refer to the type variables in the inferred type.
>   let cty1 = (cxInf ++ subst s' cxGiven, tyInf)
>   return (Typed (Just $ mirrorFBCT cty1) e' cx sig, cty1)
>   where sig' = nameSigType sig
>         eqTypes (ForAll _cx1 _ t1) (ForAll _cx2 _ t2) = t1 == t2
> tcExpr p (Paren e) = do
>   (e', cty) <- tcExpr p e
>   return (Paren e', cty)
> tcExpr p t@(Tuple sref es)
>   | null es = return $ (t, noContext unitType)
>   | otherwise = do 
>      esAndCtys <- mapM (tcExpr p) es
>      let cx = concatMap (fst . snd) esAndCtys
>          tys = map (snd . snd) esAndCtys
>          es' = map fst esAndCtys
>      return (Tuple sref es', (cx, tupleType tys))
> tcExpr p e@(List srefs es) = do 
>   tvar <- freshConstrTypeVar
>   (es', cty) <- tcElems (ppExpr 0 e) es tvar []
>   return (List srefs es', cty)
>   where tcElems :: Doc -> [Expression] -> ConstrType -> [Expression] 
>                 -> TCM ([Expression], ConstrType)
>         tcElems _ [] (cx, ty) newEs = return (reverse newEs, (cx, listType ty))
>         tcElems doc (e1:es1) cty@(cx, ty) newEs = do
>           (e1', cty'@(cx', _ty')) <- tcExpr p e1
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e1)
>                 cty cty'
>           tcElems doc es1 (cx ++ cx', ty) (e1':newEs)
> tcExpr p (ListCompr sref e qs) = do
>     tyEnv0 <- getValueEnv
>     ss <- mapM (tcQual p) qs
>     let cxs = concatMap snd ss
>         qs' = map fst ss
>     (e', (cx, ty)) <- tcExpr p e
>     cty <- checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cx ++ cxs, listType ty)
>     return (ListCompr sref e' qs', cty) 
> tcExpr p e@(EnumFrom e1) = do
>     (e1', cty1@(cx1, _ty1)) <- tcExpr p e1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     return (EnumFrom e1', (cx1, listType intType))
> tcExpr p e@(EnumFromThen e1 e2) = do
>     (e1', cty1@(cx1, _ty1)) <- tcExpr p e1
>     (e2', cty2@(cx2, _ty2)) <- tcExpr p e2
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) (noContext intType) cty2
>     return (EnumFromThen e1' e2', (cx1 ++ cx2, listType intType))
> tcExpr p e@(EnumFromTo e1 e2) = do
>     (e1', cty1@(cx1, _ty1)) <- tcExpr p e1
>     (e2', cty2@(cx2, _ty2)) <- tcExpr p e2
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) (noContext intType) cty2
>     return (EnumFromTo e1' e2', (cx1 ++ cx2, listType intType))
> tcExpr p e@(EnumFromThenTo e1 e2 e3) = do
>     (e1', cty1@(cx1, _ty1)) <- tcExpr p e1
>     (e2', cty2@(cx2, _ty2)) <- tcExpr p e2
>     (e3', cty3@(cx3, _ty3)) <- tcExpr p e3
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) (noContext intType) cty1
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) (noContext intType) cty2
>     unify p "arithmetic sequence"
>           (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) (noContext intType) cty3
>     return (EnumFromThenTo e1' e2' e3', (cx1 ++ cx2 ++ cx3, listType intType))
> tcExpr p e@(UnaryMinus op e1) = do
>     opTy <- opType op
>     (e1', cty1) <- tcExpr p e1
>     unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           opTy cty1
>     return (UnaryMinus op e1', cty1)
>   where opType op'
>           | op' == minusId  = liftM noContext $ freshConstrained [intType,floatType]
>           | op' == fminusId = return $ noContext floatType
>           | otherwise = internalError $ "TypeCheck.tcExpr unary " ++ idName op'
> tcExpr p e@(Apply e1 e2) = do
>     (e1',      (cx1,  ty1)) <- tcExpr p e1
>     (e2', cty2@(cx2, _ty2)) <- tcExpr p e2
>     (alpha,beta) <- 
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>              ty1
>     unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>           (noContext alpha) cty2
>     cx' <- adjustContext (cx1 ++ cx2)
>     return (Apply e1' e2', (cx', beta))
> tcExpr p e@(InfixApply e1 op e2) = do
>     (_op, ctyo@(cxo, opTy)) <- tcExpr p (infixOp op)
>     (e1', cty1@(cx1, _ty1)) <- tcExpr p e1
>     (e2', cty2@(cx2, _ty2)) <- tcExpr p e2
>     (alpha,beta,gamma) <-
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) opTy
>     unify p "infix application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext alpha) cty1
>     unify p "infix application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>           (noContext beta) cty2
>     cx' <- adjustContext (cxo ++ cx1 ++ cx2)
>     return (InfixApply e1' (annotInfixOpType op ctyo) e2', (cx', gamma))
> tcExpr p e@(LeftSection e1 op) = do
>     (_op, opTy@(cxo, _)) <- tcExpr p (infixOp op)
>     (e1', cty1@(cx1, _)) <- tcExpr p e1
>     (alpha,beta) <-
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               (getType opTy)
>     unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext alpha) cty1
>     cx' <- adjustContext (cxo ++ cx1)
>     return (LeftSection e1' (annotInfixOpType op opTy), (cx', beta))
> tcExpr p e@(RightSection op e1) = do
>     (_op, opTy@(cxo, _)) <- tcExpr p (infixOp op)
>     (e1', cty1@(cx1, _)) <- tcExpr p e1
>     (alpha,beta,gamma) <-
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) (getType opTy)
>     unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext beta) cty1
>     cx' <- adjustContext (cxo ++ cx1)
>     return (RightSection (annotInfixOpType op opTy) e1', (cx', TypeArrow alpha gamma))
> tcExpr p expr@(Lambda sref ts e) = do
>     tyEnv0 <- getValueEnv
>     ctys <- mapM (tcPattern p) ts
>     (e', (cx, ty)) <- tcExpr p e
>     let cxs = concat (map fst ctys ++ [cx]) 
>     cty <- checkSkolems p (text "Expression:" <+> ppExpr 0 expr) tyEnv0
>                           (cxs, foldr TypeArrow ty (map getType ctys))
>     return (Lambda sref ts e', cty)
> tcExpr p (Let ds e) = do
>     tyEnv0 <- getValueEnv
>     (ds', cxs) <- tcDecls ds
>     (e', (cx, ty)) <- tcExpr p e
>     cty <- checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cx ++ cxs, ty)
>     return (Let ds' e', cty)
> tcExpr p (Do sts e) = do
>     tyEnv0 <- getValueEnv
>     ss <- mapM (tcStmt p) sts
>     let cxs = concatMap snd ss
>         sts' = map fst ss
>     alpha <- freshTypeVar
>     (e', cty@(cx, ty)) <- tcExpr p e
>     unify p "statement" (ppExpr 0 e) (noContext $ ioType alpha) cty
>     cty' <- checkSkolems p (text "Expression:" <+> ppExpr 0 e) tyEnv0 (cxs ++ cx, ty)
>     return (Do sts' e', cty')
> tcExpr p e@(IfThenElse sref e1 e2 e3) = do
>     (e1', cty1@(cx1, _ty1)) <- tcExpr p e1
>     unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>           (noContext boolType) cty1
>     (e2', cty2@(cx2, _ty2)) <- tcExpr p e2
>     (e3', cty3@(cx3, ty3))  <- tcExpr p e3
>     unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>           cty2 cty3
>     return (IfThenElse sref e1' e2' e3', (cx1 ++ cx2 ++ cx3, ty3))
> tcExpr p (Case sref ct e alts) = do
>     tyEnv0 <- getValueEnv
>     (e', cty@(cx, _)) <- tcExpr p e
>     alpha <- freshConstrTypeVar
>     (alts', (cxA, tyA)) <- tcAlts tyEnv0 cty alpha [] alts []
>     return (Case sref ct e' alts', (cx ++ cxA, tyA))
>   where tcAlts _      _   (_, ty2) cx [] newAs = return (reverse newAs, (cx, ty2))
>         tcAlts tyEnv0 ty1 ty2 cx (alt1:alts1) newAs = do
>           (a, cx1) <- tcAlt (ppAlt alt1) tyEnv0 ty1 ty2 alt1
>           tcAlts tyEnv0 ty1 ty2 (cx ++ cx1) alts1 (a:newAs)
>         tcAlt :: Doc -> ValueEnv -> ConstrType -> ConstrType -> Alt -> TCM (Alt, BT.Context)
>         tcAlt doc tyEnv0 ty1 ty2 (Alt p1 t rhs) = do
>           ctyP@(cxP, _) <- tcPattern p1 t
>           unify p1 "case pattern" (doc $-$ text "Term:" <+> ppPattern 0 t)
>                 ty1 ctyP
>           (rhs', ctyRhs@(cxRhs, _)) <- tcRhs tyEnv0 rhs
>           unify p1 "case branch" doc ty2 ctyRhs
>           return (Alt p1 t rhs', cxP ++ cxRhs)
> tcExpr _ (RecordConstr fs) = do
>     fs'AndFts <- mapM tcFieldExpr fs 
>     let fts = map snd fs'AndFts 
>         cxs = concatMap (fst . snd) fts
>         fs' = map fst fs'AndFts
>     return (RecordConstr fs', (cxs, TypeRecord 
>       (map (\(id0, cty) -> (id0, getType cty)) fts) Nothing))
> tcExpr p r@(RecordSelection e l) = do
>     m <- getModuleIdent
>     (e', cty@(cx, _)) <- tcExpr p e
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
>     return (RecordSelection e' l, (cx', lty))
> tcExpr p r@(RecordUpdate fs e) = do
>     (e', cty) <- tcExpr p e
>     fs'AndFts   <- mapM tcFieldExpr fs
>     let fts = map snd fs'AndFts
>         fs' = map fst fs'AndFts
>     alpha <- freshVar id
>     let rty = TypeRecord (map (\(id0, cty0) -> (id0, getType cty0)) fts) (Just alpha)
>     unify p "record update" (ppExpr 0 r) cty (noContext rty)
>     return (RecordUpdate fs' e', cty)

> tcQual :: Position -> Statement -> TCM (Statement, BT.Context)
> tcQual p (StmtExpr  sref e) = do
>   (e', cty@(cx, _ty)) <- tcExpr p e
>   unify p "guard" (ppExpr 0 e) (noContext boolType) cty
>   return (StmtExpr sref e', cx)
> tcQual p q@(StmtBind sref t e) = do
>   (cx1, ty1) <- tcPattern p t
>   (e', cty2@(cx2, _  )) <- tcExpr p e
>   unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>         (noContext $ listType ty1) cty2
>   return (StmtBind sref t e', cx1 ++ cx2)
> tcQual _ (StmtDecl      ds) = do 
>   -- do not ignore contexts of declarations
>   (ds', cx) <- tcDecls ds
>   return (StmtDecl ds', cx)

> tcStmt ::Position -> Statement -> TCM (Statement, BT.Context)
> tcStmt p (StmtExpr sref e) = do
>   alpha       <- freshTypeVar
>   (e', cty@(cx, _)) <- tcExpr p e
>   unify p "statement" (ppExpr 0 e) (noContext $ ioType alpha) cty
>   return (StmtExpr sref e', cx)
> tcStmt p st@(StmtBind sref t e) = do
>   cty1@(cx1, _) <- tcPattern p t
>   (e', cty2@(cx2, _)) <- tcExpr p e
>   unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e) (noContext $ ioType $ getType cty1) cty2
>   return (StmtBind sref t e', cx1 ++ cx2)
> tcStmt _ (StmtDecl ds) = do
>   -- do not ignore contexts of declarations
>   (ds', cx) <- tcDecls ds
>   return (StmtDecl ds', cx)

> tcFieldExpr :: Field Expression -> TCM (Field Expression, (Ident, ConstrType))
> tcFieldExpr f@(Field p0 l e) = do
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
>   (e', cty) <- tcExpr p e
>   unify p "record" (text "Field:" <+> ppFieldExpr f) lty cty
>   return (Field p0 l e', (l,cty))

> adjustContext :: BT.Context -> TCM BT.Context
> adjustContext cxs = do
>   theta <- getTypeSubst
>   return (subst theta cxs) 

> reverseTySubst :: TypeSubst -> TypeSubst
> reverseTySubst = listToSubst . map swap . substToList
>   where swap (n, TypeVariable m) = (m, TypeVariable n)
>         swap _ = internalError "reverseTySubst"

> -- nubCx :: ConstrType -> ConstrType
> -- nubCx (cx, ty) = (nub $ cx, ty)

> annotInfixOpType :: InfixOp -> ConstrType -> InfixOp
> annotInfixOpType (InfixOp _ qid) cty = InfixOp (Just $ mirrorFBCT cty) qid
> annotInfixOpType (InfixConstr qid) _ = (InfixConstr qid)

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
>              -- TODO: don't throw an internal error correct?
>              -- there are situations where an internal error should not
>              -- be thrown because if the program is not type correct this
>              -- case can occur (for an example see "BugTypedExpr.curry"!) 
>              -- internalError ("instContext too big " ++ show x ++ " " ++ show tys ++ " " ++ show cx)
>              then TypeVariable x 
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

> genS :: Set.Set Int -> ConstrType -> (TypeScheme, TypeSubst)
> genS gvs (cx, ty) = (ForAll (subst s cx) (length tvs)
>                             (subst s ty), s)
>   where tvs = [tv | tv <- nub (typeVars ty), tv `Set.notMember` gvs]
>         tvs' = map TypeVariable [0 ..]
>         s = foldr2 bindSubst idSubst tvs tvs'

> gen :: Set.Set Int -> ConstrType -> TypeScheme
> gen gvs = fst . genS gvs

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

> funType :: ModuleIdent -> QualIdent -> ValueEnv -> TypeScheme
> funType m f tyEnv = case qualLookupValue f tyEnv of
>   [Value _ _ sigma] -> sigma
>   _ -> case qualLookupValue (qualQualify m f) tyEnv of
>     [Value _ _ sigma] -> sigma
>     _ -> internalError $ "TypeCheck.funType function not found: " 
>            ++ show f ++ ", more precisely " ++ show (unqualify f)

> sureLabelType :: Ident -> ValueEnv -> Maybe TypeScheme
> sureLabelType l tyEnv = case lookupValue l tyEnv of
>   Label _ _ sigma : _ -> Just sigma
>   _ -> Nothing

> bindFunOnce :: ModuleIdent -> Ident -> Int -> TypeScheme
>                 -> ValueEnv -> ValueEnv
> bindFunOnce m f n ty env = 
>   maybe env id $ tryBindFun m f n ty env

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

> -- | The boolean flag states whether the types should be expanded by
> -- expandType. This must be disabled for type signatures in the second
> -- run of the type checker. 
> expandPolyType :: Bool -> BaseConstrType -> TCM TypeScheme
> expandPolyType expType ty
>   = (\(cx, ty0) -> (polyType (normalize ty0) `constrainBy` cx)) `liftM` expandMonoType expType [] ty

> expandMonoType :: Bool -> [Ident] -> BaseConstrType -> TCM ConstrType
> expandMonoType expType tvs ty = do
>   m <- getModuleIdent
>   tcEnv <- getTyConsEnv
>   return $ expandMonoType' m tcEnv tvs expType ty

> expandMonoType' :: ModuleIdent -> TCEnv -> [Ident] -> Bool -> BaseConstrType -> ConstrType
> expandMonoType' m tcEnv tvs expType ty = 
>   (cx, if not expType then ty' else expandType m tcEnv ty')
>   where (cx, ty') = (toConstrType tvs ty)

> expandMonoTypes :: ModuleIdent -> TCEnv -> [Ident] -> Bool -> [BaseConstrType] -> [ConstrType]
> expandMonoTypes m tcEnv tvs expType tys 
>   = map (\(cx, ty) -> 
>             (cx, if not expType then ty else expandType m tcEnv ty))
>       (toConstrTypes tvs tys)

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
> localTypes tyEnv = [ty | (_, Value _ _ (ForAll _cx _ ty)) <- localBindings tyEnv]

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
>   , text "Type signature:" <+> ppContext cx <+> ppTypeExpr 0 ty
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

> {-
> errEqualClassMethodAndFunctionNames :: ModuleIdent -> Ident -> Doc
> errEqualClassMethodAndFunctionNames _m f = 
>   text "Equal class method and top level function names: " <> ppIdent f
> -}

> {-
> errAmbiguousTypeVarsInContext :: Position -> Ident -> [Int] -> Message
> errAmbiguousTypeVarsInContext p f _tvars = 
>   posMessage p (text "Ambiguous type variables in the context to function"
>   <+> text (show f))
> -}

> errContextImplication :: Position -> ModuleIdent -> BT.Context -> BT.Context 
>                       -> BT.Context -> Ident -> Message
> errContextImplication p m cx cx' cx'' id0 = posMessage p $ 
>   text "Given context" <+> ppContext' m cx <+> text "doesn't imply inferred context"
>   <+> ppContext' m cx' <+> text "in type signature of" <+> text (show id0) <> text ":"
>   $$ ppContext' m cx'' <+> text "is not implied. " 

> errNoInstance :: Position -> ModuleIdent -> BT.Context -> Message
> errNoInstance p m cx = posMessage p $
>   text "No instances for: " <> ppContext' m cx

> errAmbiguousContextElems :: Position -> ModuleIdent -> Ident -> [(QualIdent, Type)] -> Message
> errAmbiguousContextElems p m v cx = posMessage p $ 
>   text "Ambiguous type variables in the following context elements of function"
>   <+> text (escName v) <> text ": "
>   $$ text (show (ppContext' m cx))

\end{verbatim}
The following functions implement pretty-printing for types.
\begin{verbatim}

> ppType :: ModuleIdent -> Type -> Doc
> ppType m = ppTypeExpr 0 . fromQualType m

> ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
> ppTypeScheme m (ForAll cx _ ty) = ppContext' m cx <+> text "=>" <+> ppType m ty

> ppContext' :: ModuleIdent -> BT.Context -> Doc
> ppContext' m cx = parens $ hsep $ 
>   punctuate comma (map (\(qid, ty) -> ppQIdent qid <+> (ps ty) (ppType m ty)) cx')
>   where cx' = nub cx
>         ps (TypeConstructor _ (_:_)) = parens
>         ps (TypeArrow _ _) = parens
>         ps _ = id
>            

\end{verbatim}
After all type checking has been done, check at last, that there are 
no class methods with the name of one of the top level functions. 
\begin{verbatim}

> -- | checks that there are no class methods and function names with the
> -- same name
> {-
> checkNoEqualClassMethodAndFunctionNames :: ValueEnv -> ClassEnv -> TCM ()
> checkNoEqualClassMethodAndFunctionNames vEnv cEnv = do
>   let classMethods = getAllClassMethodNames cEnv
>   mapM_ searchClassMethod classMethods
>   where
>   searchClassMethod f 
>     = if not $ null $ lookupValue f vEnv -- TODO: use also qualLookupValue?
>       then do
>         m <- getModuleIdent
>         report $ message $ errEqualClassMethodAndFunctionNames m f
>       else return ()
> -}

\end{verbatim}
Also check that in the top level declarations there are no ambiguous type
vars in their contexts.
\begin{verbatim} 

> {-
> checkForAmbiguousContexts :: [Decl] -> TCM ()
> checkForAmbiguousContexts decls = mapM_ check' (filter isFunctionDecl decls)
>   where
>   check' :: Decl -> TCM ()
>   check' (FunctionDecl p _ _ f _) = do
>     vEnv <- getValueEnv
>     let tsc = lookupValue f vEnv
>     case tsc of
>       [] -> internalError "checkForAmbiguousContexts 1"
>       [Value _ _ (ForAll cx _ _)] -> do
>          let ambiguous = ambiguousTypeVars cx
>          case null $ ambiguous of
>            True -> return ()
>            False -> report $ errAmbiguousTypeVarsInContext p f ambiguous
>       _ -> return ()
>   check' _ = internalError "checkForAmbiguousContexts 3"
>   ambiguousTypeVars :: BT.Context -> [Int]
>   ambiguousTypeVars = filter ( < 0) . concatMap (typeVars . snd)
> -}

\end{verbatim}
After the type checking has finished, we still have to apply the final
type substitution to the recorded contexts and types (at the moment for patterns
nothing is recorded so that they are simply returned). 
\begin{verbatim}

> applyTypeSubst :: TypeSubst -> [Decl] -> [Decl]
> applyTypeSubst theta ds = map (tsDecl theta) ds

> tsDecl :: TypeSubst -> Decl -> Decl
> tsDecl _theta d@(InfixDecl _ _ _ _) = d
> tsDecl _theta d@(DataDecl _ _ _ _)  = d
> tsDecl _theta d@(NewtypeDecl _ _ _ _) = d
> tsDecl _theta d@(TypeDecl _ _ _ _) = d
> tsDecl _theta d@(TypeSig _ _ _ _) = d
> tsDecl theta (FunctionDecl p (Just cty) n id0 eqs) 
>   = FunctionDecl p (Just $ subst' theta cty)  n id0 (map (tsEqu theta) eqs)
> tsDecl _theta (FunctionDecl _ Nothing _ _ _) = internalError "tsDecl FunctionDecl"
> tsDecl _theta d@(ForeignDecl _ _ _ _ _) = d
> tsDecl _theta d@(ExternalDecl _ _) = d
> tsDecl theta (PatternDecl p (Just cty) n pt rhs) 
>   = PatternDecl p (Just $ subst' theta cty) n pt (tsRhs theta rhs)
> tsDecl _theta (PatternDecl _ Nothing _ _ _) = internalError "tsDecl PatternDecl"
> tsDecl _theta d@(FreeDecl _ _) = d
> tsDecl _theta d@(ClassDecl _ _ _ _ _) = d
> tsDecl _theta d@(InstanceDecl _ _ _ _ _ _) = d
   
> tsEqu :: TypeSubst -> Equation -> Equation
> -- lhs only contains patterns, hence we do not need to include this
> tsEqu theta (Equation p lhs rhs) = Equation p lhs (tsRhs theta rhs)

> tsRhs :: TypeSubst -> Rhs -> Rhs
> tsRhs theta (SimpleRhs p e ds) 
>   = SimpleRhs p (tsExpr theta e) (map (tsDecl theta) ds)
> tsRhs theta (GuardedRhs ces ds)
>   = GuardedRhs (map (tsCondExpr theta) ces) (map (tsDecl theta) ds)

> tsCondExpr :: TypeSubst -> CondExpr -> CondExpr
> tsCondExpr theta (CondExpr p e1 e2) 
>   = CondExpr p (tsExpr theta e1) (tsExpr theta e2)

> tsExpr :: TypeSubst -> Expression -> Expression
> tsExpr _theta e@(Literal _) = e
> tsExpr theta (Variable (Just cty) i) = Variable (Just $ subst' theta cty) i
> tsExpr _theta (Variable Nothing _) = internalError "tsExpr Variable"
> tsExpr _theta e@(Constructor _) = e
> tsExpr theta (Paren e) = Paren (tsExpr theta e) 
> tsExpr theta (Typed cty e c t) = Typed cty (tsExpr theta e) c t
> tsExpr theta (Tuple sref es) = Tuple sref (map (tsExpr theta) es)
> tsExpr theta (List srefs es) = List srefs (map (tsExpr theta) es)
> tsExpr theta (ListCompr sref e ss) 
>   = ListCompr sref (tsExpr theta e) (map (tsStmt theta) ss)
> tsExpr theta (EnumFrom e1) = EnumFrom (tsExpr theta e1)
> tsExpr theta (EnumFromThen e1 e2) = EnumFromThen (tsExpr theta e1) (tsExpr theta e2)
> tsExpr theta (EnumFromTo e1 e2) = EnumFromTo (tsExpr theta e1) (tsExpr theta e2)
> tsExpr theta (EnumFromThenTo e1 e2 e3) = EnumFromThenTo (tsExpr theta e1) (tsExpr theta e2) (tsExpr theta e3)
> tsExpr theta (UnaryMinus i e) = UnaryMinus i (tsExpr theta e)
> tsExpr theta (Apply e1 e2) = Apply (tsExpr theta e1) (tsExpr theta e2)
> tsExpr theta (InfixApply e1 op e2) 
>   = InfixApply (tsExpr theta e1) (tsInfixOp theta op) (tsExpr theta e2)
> tsExpr theta (LeftSection e op) = LeftSection (tsExpr theta e) (tsInfixOp theta op)
> tsExpr theta (RightSection op e) = RightSection (tsInfixOp theta op) (tsExpr theta e)
> tsExpr theta (Lambda sref ps e) = Lambda sref ps (tsExpr theta e)
> tsExpr theta (Let ds e) = Let (map (tsDecl theta) ds) (tsExpr theta e)
> tsExpr theta (Do ss e) = Do (map (tsStmt theta) ss) (tsExpr theta e)
> tsExpr theta (IfThenElse sref e1 e2 e3)
>   = IfThenElse sref (tsExpr theta e1) (tsExpr theta e2) (tsExpr theta e3)
> tsExpr theta (Case sref ct e alts) 
>   = Case sref ct (tsExpr theta e) (map (tsAlt theta) alts)
> tsExpr theta (RecordConstr fs) = RecordConstr (map (tsField theta) fs)
> tsExpr theta (RecordSelection e i) = RecordSelection (tsExpr theta e) i
> tsExpr theta (RecordUpdate fs e) 
>   = RecordUpdate (map (tsField theta) fs) (tsExpr theta e)

> tsStmt :: TypeSubst -> Statement -> Statement
> tsStmt theta (StmtExpr sref e) = StmtExpr sref (tsExpr theta e)
> tsStmt theta (StmtDecl ds) = StmtDecl (map (tsDecl theta) ds)
> tsStmt theta (StmtBind sref p e) = StmtBind sref p (tsExpr theta e)

> tsAlt :: TypeSubst -> Alt -> Alt
> tsAlt theta (Alt p pt rhs) = Alt p pt (tsRhs theta rhs)

> tsField :: TypeSubst -> Field Expression -> Field Expression
> tsField theta (Field p i e) = Field p i (tsExpr theta e)

> tsInfixOp :: TypeSubst -> InfixOp -> InfixOp
> tsInfixOp theta (InfixOp (Just cty) qid) = InfixOp (Just $ subst' theta cty) qid
> tsInfixOp _theta (InfixOp Nothing _) = internalError "tsInfixOp"
> tsInfixOp _theta (InfixConstr qid) = InfixConstr qid 

> subst' :: TypeSubst -> ConstrType_ -> ConstrType_
> subst' s ty = mirrorFBCT $ subst s $ mirrorBFCT ty

\end{verbatim}
The declarations are numbered, so that each declaration has a unique id. That
is important because we want to store data for each declaration group, so we
have to use a unique id for each declaration group. One could use the function
names, but unfortunately pattern declarations don't have a function name. Thus 
we have to use other unique ids.  
\begin{verbatim}

> -- | numbers all declarations subsequently with unique ids, descending in
> -- the tree to reach all declarations (also e.g. in statements or let 
> -- expresssions 
> numberDecls :: [Decl] -> TCM [Decl]
> numberDecls ds = mapM numberDecl ds

> numberDecl :: Decl -> TCM Decl
> numberDecl (FunctionDecl p cty _ f eqs) = do
>   n <- getNextDeclCounter
>   eqs' <- mapM numberEqu eqs
>   return $ FunctionDecl p cty n f eqs' 
> numberDecl (PatternDecl p cty _ pt rhs) = do
>   n <- getNextDeclCounter
>   rhs' <- numberRhs rhs
>   return $ PatternDecl p cty n pt rhs'
> numberDecl d = return d 

> numberEqu :: Equation -> TCM Equation
> numberEqu (Equation p lhs rhs) = Equation p lhs `liftM` numberRhs rhs

> numberRhs :: Rhs -> TCM Rhs
> numberRhs (SimpleRhs p e ds) = liftM2 (SimpleRhs p) (numberExpr e) (numberDecls ds)
> numberRhs (GuardedRhs ces ds) = liftM2 GuardedRhs (mapM numberCExpr ces) (numberDecls ds)

> numberCExpr :: CondExpr -> TCM CondExpr
> numberCExpr (CondExpr p e1 e2) = liftM2 (CondExpr p) (numberExpr e1) (numberExpr e2)

> numberExpr :: Expression -> TCM Expression
> numberExpr l@(Literal _) = return l
> numberExpr v@(Variable _ _) = return v
> numberExpr c@(Constructor _) = return c
> numberExpr (Paren e) = Paren `liftM` numberExpr e
> numberExpr (Typed cty e cx ty) = liftM3 (Typed cty) (numberExpr e) (return cx) (return ty)
> numberExpr (Tuple sref es) = Tuple sref `liftM` mapM numberExpr es
> numberExpr (List sref es) = List sref `liftM` mapM numberExpr es
> numberExpr (ListCompr sref e ss) = liftM2 (ListCompr sref) (numberExpr e) (mapM numberStmt ss)
> numberExpr (EnumFrom e1) = EnumFrom `liftM` numberExpr e1
> numberExpr (EnumFromThen e1 e2) = liftM2 EnumFromThen (numberExpr e1) (numberExpr e2)
> numberExpr (EnumFromTo e1 e2) = liftM2 EnumFromTo (numberExpr e1) (numberExpr e2)
> numberExpr (EnumFromThenTo e1 e2 e3) = liftM3 EnumFromThenTo (numberExpr e1) (numberExpr e2) (numberExpr e3)
> numberExpr (UnaryMinus i e) = UnaryMinus i `liftM` numberExpr e
> numberExpr (Apply e1 e2) = liftM2 Apply (numberExpr e1) (numberExpr e2) 
> numberExpr (InfixApply e1 op e2) = liftM3 InfixApply (numberExpr e1) (return op) (numberExpr e2)
> numberExpr (LeftSection e op) = flip LeftSection op `liftM` numberExpr e 
> numberExpr (RightSection op e) = RightSection op `liftM` numberExpr e
> numberExpr (Lambda sref ps e) = Lambda sref ps `liftM` numberExpr e
> numberExpr (Let ds e) = liftM2 Let (numberDecls ds) (numberExpr e) 
> numberExpr (Do ss e) = liftM2 Do (mapM numberStmt ss) (numberExpr e)
> numberExpr (IfThenElse sref e1 e2 e3) 
>   = liftM3 (IfThenElse sref) (numberExpr e1) (numberExpr e2) (numberExpr e3)
> numberExpr (Case sref cty e alts) = liftM2 (Case sref cty) (numberExpr e) (mapM numberAlt alts)
> numberExpr (RecordConstr fs) = RecordConstr `liftM` (mapM numberField fs)
> numberExpr (RecordSelection e i) = flip RecordSelection i `liftM` numberExpr e 
> numberExpr (RecordUpdate fs e) = liftM2 RecordUpdate (mapM numberField fs) (numberExpr e)
 
> numberStmt :: Statement -> TCM Statement
> numberStmt (StmtExpr sref e) = StmtExpr sref `liftM` numberExpr e
> numberStmt (StmtDecl ds) = StmtDecl `liftM` numberDecls ds
> numberStmt (StmtBind sref p e) = StmtBind sref p `liftM` (numberExpr e)

> numberAlt :: Alt -> TCM Alt
> numberAlt (Alt p pt rhs) = Alt p pt `liftM` numberRhs rhs

> numberField :: Field Expression -> TCM (Field Expression)
> numberField (Field p i e) = Field p i `liftM` numberExpr e

> -- |returns the unique id assigned to a function or pattern declaration
> getUniqueId :: Decl -> Int
> getUniqueId (FunctionDecl _ _ n _ _) = n
> getUniqueId (PatternDecl _ _ n _ _) = n
> getUniqueId _ = internalError "getUniqueId"

\end{verbatim}



