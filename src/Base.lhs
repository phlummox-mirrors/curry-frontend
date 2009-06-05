% $Id: Base.lhs,v 1.77 2004/02/15 22:10:25 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{Base.lhs}
\section{Common Definitions for the Compiler}
The module \texttt{Base} provides common definitions for the various 
phases of the compiler.
\begin{verbatim}

> module Base(module Base,module Ident,module Position,module Types,
>             module CurrySyntax) where
> import Ident
> import Position
> import Types
> import CurrySyntax
> import CurryPP
> import Pretty
> import FlatWithSrcRefs hiding (SrcRef, Fixity(..), TypeExpr, Expr(..))
> import Env
> import TopEnv
> import List
> import Map
> import Monad
> import Set
> import Utils
> import Maybe

> import qualified FlatWithSrcRefs (Fixity(..), TypeExpr)

\end{verbatim}
\paragraph{Types}
The functions \texttt{toType}, \texttt{toTypes}, and \texttt{fromType}
convert Curry type expressions into types and vice versa. The
functions \texttt{qualifyType} and \texttt{unqualifyType} add and
remove module qualifiers in a type, respectively.

When Curry type expression are converted with \texttt{toType} or
\texttt{toTypes}, type variables are assigned ascending indices in the
order of their occurrence. It is possible to pass a list of additional
type variables to both functions which are assigned indices before
those variables occurring in the type. This allows preserving the
order of type variables in the left hand side of a type declaration.
\begin{verbatim}

> toQualType :: ModuleIdent -> [Ident] -> TypeExpr -> Type
> toQualType m tvs ty = qualifyType m (toType tvs ty)

> toQualTypes :: ModuleIdent -> [Ident] -> [TypeExpr] -> [Type]
> toQualTypes m tvs tys = map (qualifyType m) (toTypes tvs tys)

> toType :: [Ident] -> TypeExpr -> Type
> toType tvs ty = toType' (fromListFM (zip (tvs ++ tvs') [0..])) ty
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> toTypes :: [Ident] -> [TypeExpr] -> [Type]
> toTypes tvs tys = map (toType' (fromListFM (zip (tvs ++ tvs') [0..]))) tys
>   where tvs' = [tv | tv <- nub (concatMap fv tys), tv `notElem` tvs]

> toType' :: FM Ident Int -> TypeExpr -> Type
> toType' tvs (ConstructorType tc tys) =
>   TypeConstructor tc (map (toType' tvs) tys)
> toType' tvs (VariableType tv) =
>   maybe (internalError ("toType " ++ show tv)) TypeVariable (lookupFM tv tvs)
> toType' tvs (TupleType tys)
>   | null tys = TypeConstructor (qualify unitId) []
>   | otherwise = TypeConstructor (qualify (tupleId (length tys'))) tys'
>   where tys' = map (toType' tvs) tys
> toType' tvs (ListType ty) = TypeConstructor (qualify listId) [toType' tvs ty]
> toType' tvs (ArrowType ty1 ty2) =
>   TypeArrow (toType' tvs ty1) (toType' tvs ty2)
> toType' tvs (RecordType fs rty) =
>   TypeRecord (concatMap (\ (ls,ty) -> map (\l -> (l, toType' tvs ty)) ls) fs)
>              (maybe Nothing 
>	              (\ty -> case toType' tvs ty of
>	                        TypeVariable tv -> Just tv 
>	                        _ -> internalError ("toType " ++ show ty))
>	              rty)

> qualifyType :: ModuleIdent -> Type -> Type
> qualifyType m (TypeConstructor tc tys)
>   | isTupleId tc' = tupleType tys'
>   | tc' == unitId && n == 0 = unitType
>   | tc' == listId && n == 1 = listType (head tys')
>   | otherwise = TypeConstructor (qualQualify m tc) tys'
>   where n = length tys'
>         tc' = unqualify tc
>         tys' = map (qualifyType m) tys
> qualifyType _ (TypeVariable tv) = TypeVariable tv
> qualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (qualifyType m) tys) tv
> qualifyType m (TypeArrow ty1 ty2) =
>   TypeArrow (qualifyType m ty1) (qualifyType m ty2)
> qualifyType _ (TypeSkolem k) = TypeSkolem k
> qualifyType m (TypeRecord fs rty) =
>   TypeRecord (map (\ (l,ty) -> (l, qualifyType m ty)) fs) rty

> fromQualType :: ModuleIdent -> Type -> TypeExpr
> fromQualType m ty = fromType (unqualifyType m ty)

> fromType :: Type -> TypeExpr
> fromType (TypeConstructor tc tys)
>   | isTupleId c = TupleType tys'
>   | c == listId && length tys == 1 = ListType (head tys')
>   | c == unitId && null tys = TupleType []
>   | otherwise = ConstructorType tc tys'
>   where c = unqualify tc
>         tys' = map (fromType) tys
> fromType (TypeVariable tv) =
>   VariableType (if tv >= 0 then nameSupply !! tv
>                            else mkIdent ('_' : show (-tv)))
> fromType (TypeConstrained tys _) = fromType (head tys)
> fromType (TypeArrow ty1 ty2) = ArrowType (fromType ty1) (fromType ty2)
> fromType (TypeSkolem k) = VariableType (mkIdent ("_?" ++ show k))
> fromType (TypeRecord fs rty) = 
>   RecordType (map (\ (l,ty) -> ([l], fromType ty)) fs)
>              (maybe Nothing (Just . fromType . TypeVariable) rty)

> unqualifyType :: ModuleIdent -> Type -> Type
> unqualifyType m (TypeConstructor tc tys) =
>   TypeConstructor (qualUnqualify m tc) (map (unqualifyType m) tys)
> unqualifyType _ (TypeVariable tv) = TypeVariable tv
> unqualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (unqualifyType m) tys) tv
> unqualifyType m (TypeArrow ty1 ty2) =
>   TypeArrow (unqualifyType m ty1) (unqualifyType m ty2)
> unqualifyType m (TypeSkolem k) = TypeSkolem k
> unqualifyType m (TypeRecord fs rty) =
>   TypeRecord (map (\ (l,ty) -> (l, unqualifyType m ty)) fs) rty

\end{verbatim}
The following functions implement pretty-printing for types.
\begin{verbatim}

> ppType :: ModuleIdent -> Type -> Doc
> ppType m = ppTypeExpr 0 . fromQualType m

> ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
> ppTypeScheme m (ForAll _ ty) = ppType m ty

\end{verbatim}
\paragraph{Interfaces}
The compiler maintains a global environment holding all (directly or
indirectly) imported interfaces.

The function \texttt{bindFlatInterfac} transforms FlatInterface
information (type \texttt{FlatCurry.Prog} to MCC interface declarations
(type \texttt{CurrySyntax.IDecl}. This is necessary to process
FlatInterfaces instead of ".icurry" files when using MCC as frontend
for PAKCS.
\begin{verbatim}

> type ModuleEnv = Env ModuleIdent [IDecl]

> bindModule :: Interface -> ModuleEnv -> ModuleEnv
> bindModule (Interface m ds) = bindEnv m ds

> bindFlatInterface :: Prog -> ModuleEnv -> ModuleEnv
> bindFlatInterface (Prog m imps ts fs os)
>    = bindModule (Interface (mkMIdent [m])
>	                     ((map genIImportDecl imps)
>		              ++ (map genITypeDecl ts')
>		              ++ (map genIFuncDecl fs)
>		              ++ (map genIOpDecl os)))
>  where
>  genIImportDecl :: String -> IDecl
>  genIImportDecl imp = IImportDecl pos (mkMIdent [imp])
>
>  genITypeDecl :: TypeDecl -> IDecl
>  genITypeDecl (Type qn _ is cs)
>     | recordExt `isPrefixOf` snd qn
>       = ITypeDecl pos
>                   (genQualIdent qn)
>	            (map (genVarIndexIdent "a") is)
>	            (RecordType (map genLabeledType cs) Nothing)
>     | otherwise
>       = IDataDecl pos 
>                   (genQualIdent qn) 
>                   (map (genVarIndexIdent "a") is) 
>                   (map (Just . genConstrDecl) cs)
>  genITypeDecl (TypeSyn qn _ is t)
>     = ITypeDecl pos
>                 (genQualIdent qn)
>                 (map (genVarIndexIdent "a") is)
>                 (genTypeExpr t)
>
>  genIFuncDecl :: FuncDecl -> IDecl
>  genIFuncDecl (Func qn a _ t _) 
>     = IFunctionDecl pos (genQualIdent qn) a (genTypeExpr t)
>
>  genIOpDecl :: OpDecl -> IDecl
>  genIOpDecl (Op qn f p) = IInfixDecl pos (genInfix f) p  (genQualIdent qn)
>
>  genConstrDecl :: ConsDecl -> ConstrDecl
>  genConstrDecl (Cons qn _ _ ts)
>     = ConstrDecl pos [] (mkIdent (snd qn)) (map genTypeExpr ts)
>
>  genLabeledType :: FlatWithSrcRefs.ConsDecl -> ([Ident],CurrySyntax.TypeExpr)
>  genLabeledType (Cons (q,n) _ _ [t])
>     = ([renameLabel (fromLabelExtId (mkIdent n))], genTypeExpr t)
>
>  genTypeExpr :: FlatWithSrcRefs.TypeExpr -> CurrySyntax.TypeExpr
>  genTypeExpr (TVar i)
>     = VariableType (genVarIndexIdent "a" i)
>  genTypeExpr (FuncType t1 t2) 
>     = ArrowType (genTypeExpr t1) (genTypeExpr t2)
>  genTypeExpr (TCons qn ts) 
>     = ConstructorType (genQualIdent qn) (map genTypeExpr ts)
>
>  genInfix :: FlatWithSrcRefs.Fixity -> Infix
>  genInfix FlatWithSrcRefs.InfixOp  = Infix
>  genInfix FlatWithSrcRefs.InfixlOp = InfixL
>  genInfix FlatWithSrcRefs.InfixrOp = InfixR
>
>  genQualIdent :: QName -> QualIdent
>  genQualIdent (mod,name) = qualifyWith (mkMIdent [mod]) (mkIdent name)
>
>  genVarIndexIdent :: String -> Int -> Ident
>  genVarIndexIdent v i = mkIdent (v ++ show i)
>
>  isSpecialPreludeType :: TypeDecl -> Bool
>  isSpecialPreludeType (Type (mod,name) _ _ _) 
>     = (name == "[]" || name == "()") && mod == "Prelude"
>  isSpecialPreludeType _ = False
>
>  pos = first m
>  ts' = filter (not . isSpecialPreludeType) ts

> lookupModule :: ModuleIdent -> ModuleEnv -> Maybe [IDecl]
> lookupModule = lookupEnv

\end{verbatim}
The label environment is used to store information of labels.
Unlike unsual identifiers like in functions, types etc. identifiers
of labels are always represented unqualified. Since the common type 
environment (type \texttt{ValueEnv}) has some problems with handling 
imported unqualified identifiers, it is necessary to process the type 
information for labels seperately.
\begin{verbatim}

> data LabelInfo = LabelType Ident QualIdent Type deriving Show

> type LabelEnv = Env Ident [LabelInfo]

> bindLabelType :: Ident -> QualIdent -> Type -> LabelEnv -> LabelEnv
> bindLabelType l r ty lEnv =
>   maybe (bindEnv l [LabelType l r ty] lEnv)
>         (\ls -> bindEnv l ((LabelType l r ty):ls) lEnv)
>         (lookupEnv l lEnv)

> lookupLabelType :: Ident -> LabelEnv -> [LabelInfo]
> lookupLabelType l lEnv = fromMaybe [] (lookupEnv l lEnv)

> initLabelEnv :: LabelEnv
> initLabelEnv = emptyEnv


\end{verbatim}
\paragraph{Type constructors}
For all defined types the compiler must maintain kind information. At
present, Curry does not support type classes. Therefore its type
language is first order and the only information that must be recorded
is the arity of each type. For algebraic data types and renaming types
the compiler also records all data constructors belonging to that
type, for alias types the type expression to be expanded is saved. In
order to manage the import and export of types, the names of the
original definitions are also recorded. On import two types are
considered equal if their original names match.

The information for a data constructor comprises the number of
existentially quantified type variables and the list of the argument
types. Note that renaming type constructors have only one type
argument.

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type. When only some
constructors of a data type are hidden, those constructors are
replaced by underscores in the interface. Furthermore, if the
right-most constructors of a data type are hidden, they are not
exported at all in order to make the interface more stable against
changes which are private to the module.
\begin{verbatim}

> data TypeInfo = DataType QualIdent Int [Maybe (Data [Type])]
>               | RenamingType QualIdent Int (Data Type)
>               | AliasType QualIdent Int Type
>               deriving Show

> data Data a = Data Ident Int a deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _) = tc
>   merge (DataType tc n cs) (DataType tc' _ cs')
>     | tc == tc' = Just (DataType tc n (mergeData cs cs'))
>     where mergeData ds [] = ds
>           mergeData [] ds = ds
>           mergeData (d:ds) (d':ds') = d `mplus` d' : mergeData ds ds'
>   merge (DataType tc n _) (RenamingType tc' _ nc)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (DataType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (RenamingType tc n nc) (RenamingType tc' _ _)
>     | tc == tc' = Just (RenamingType tc n nc)
>   merge (AliasType tc n ty) (AliasType tc' _ _)
>     | tc == tc' = Just (AliasType tc n ty)
>   merge _ _ = Nothing

> tcArity :: TypeInfo -> Int
> tcArity (DataType _ n _) = n
> tcArity (RenamingType _ n _) = n
> tcArity (AliasType _ n _) = n

\end{verbatim}
Types can only be defined on the top-level; no nested environments are
needed for them. Tuple types must be handled as a special case because
there is an infinite number of potential tuple types making it
impossible to insert them into the environment in advance.
\begin{verbatim}

> type TCEnv = TopEnv TypeInfo

> bindTypeInfo :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent
>              -> Ident -> [Ident] -> a -> TCEnv -> TCEnv
> bindTypeInfo f m tc tvs x 
>   = bindTopEnv "Base.bindTypeInfo" tc t 
>     . qualBindTopEnv "Base.bindTypeInfo" tc' t
>   where tc' = qualifyWith m tc
>         t = f tc' (length tvs) x

> lookupTC :: Ident -> TCEnv -> [TypeInfo]
> lookupTC tc tcEnv = lookupTopEnv tc tcEnv ++! lookupTupleTC tc

> qualLookupTC :: QualIdent -> TCEnv -> [TypeInfo]
> qualLookupTC tc tcEnv =
>   qualLookupTopEnv tc tcEnv ++! lookupTupleTC (unqualify tc)

> lookupTupleTC :: Ident -> [TypeInfo]
> lookupTupleTC tc
>   | isTupleId tc = [tupleTCs !! (tupleArity tc - 2)]
>   | otherwise = []

> tupleTCs :: [TypeInfo]
> tupleTCs = map typeInfo tupleData
>   where typeInfo (Data c _ tys) =
>           DataType (qualifyWith preludeMIdent c) (length tys)
>                    [Just (Data c 0 tys)]

> tupleData :: [Data [Type]]
> tupleData = [Data (tupleId n) 0 (take n tvs) | n <- [2..]]
>   where tvs = map typeVar [0..]

\end{verbatim}
\paragraph{Function and constructor types}
In order to test the type correctness of a module, the compiler needs
to determine the type of every data constructor, function,
variable, record and label in the module. 
For the purpose of type checking there is no
need for distinguishing between variables and functions. For all objects
their original names and their types are saved. Functions also
contain arity information. Labels currently contain the name of their
defining record. On import two values
are considered equal if their original names match.
\begin{verbatim}

> data ValueInfo = DataConstructor QualIdent ExistTypeScheme
>                | NewtypeConstructor QualIdent ExistTypeScheme
>                | Value QualIdent TypeScheme
>	         | Label QualIdent QualIdent TypeScheme
>	           -- Label <label> <record name> <type>
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor origName _) = origName
>   origName (NewtypeConstructor origName _) = origName
>   origName (Value origName _) = origName
>   origName (Label origName _ _) = origName
>   
>   merge (Label l r ty) (Label l' r' ty')
>     | l == l' && r == r' = Just (Label l r ty)
>     | otherwise = Nothing
>   merge x y
>     | origName x == origName y = Just x
>     | otherwise = Nothing


\end{verbatim}
Even though value declarations may be nested, the compiler uses only
flat environments for saving type information. This is possible
because all identifiers are renamed by the compiler. Here we need
special cases for handling tuple constructors.

\em{Note:} the function \texttt{qualLookupValue} has been extended to
allow the usage of the qualified list constructor \texttt{(Prelude.:)}.
\begin{verbatim}

> type ValueEnv = TopEnv ValueInfo

> bindGlobalInfo :: (QualIdent -> a -> ValueInfo) -> ModuleIdent -> Ident -> a
>                -> ValueEnv -> ValueEnv
> bindGlobalInfo f m c ty 
>   = bindTopEnv "Base.bindGlobalInfo" c v 
>     . qualBindTopEnv "Base.bindGlobalInfo" c' v
>   where c' = qualifyWith m c
>         v = f c' ty

> bindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> bindFun m f ty tyEnv
>   | uniqueId f == 0 
>     = bindTopEnv "Base.bindFun" f v (qualBindTopEnv "Base.bindFun" f' v tyEnv)
>   | otherwise = bindTopEnv "Base.bindFun" f v tyEnv
>   where f' = qualifyWith m f
>         v = Value f' ty

> rebindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> rebindFun m f ty
>   | uniqueId f == 0 = rebindTopEnv f v . qualRebindTopEnv f' v
>   | otherwise = rebindTopEnv f v
>   where f' = qualifyWith m f
>         v = Value f' ty

> bindLabel :: Ident -> QualIdent -> TypeScheme -> ValueEnv -> ValueEnv
> bindLabel l r ty tyEnv = bindTopEnv "Base.bindLabel" l v tyEnv
>   where v  = Label (qualify l) r ty

> lookupValue :: Ident -> ValueEnv -> [ValueInfo]
> lookupValue x tyEnv = lookupTopEnv x tyEnv ++! lookupTuple x

> qualLookupValue :: QualIdent -> ValueEnv -> [ValueInfo]
> qualLookupValue x tyEnv =
>   qualLookupTopEnv x tyEnv 
>   ++! qualLookupCons x tyEnv
>   ++! lookupTuple (unqualify x)

> qualLookupCons :: QualIdent -> ValueEnv -> [ValueInfo]
> qualLookupCons x tyEnv
>    | (maybe False ((==) preludeMIdent) mmid) && (id == consId)
>       = qualLookupTopEnv (qualify id) tyEnv
>    | otherwise = []
>  where (mmid, id) = splitQualIdent x

> lookupTuple :: Ident -> [ValueInfo]
> lookupTuple c
>   | isTupleId c = [tupleDCs !! (tupleArity c - 2)]
>   | otherwise = []

> tupleDCs :: [ValueInfo]
> tupleDCs = map dataInfo tupleTCs
>   where dataInfo (DataType tc tvs [Just (Data c _ tys)]) =
>           DataConstructor (qualUnqualify preludeMIdent tc)
>                           (ForAllExist (length tys) 0
>                                        (foldr TypeArrow (tupleType tys) tys))

\end{verbatim}
\paragraph{Arity}
In order to generate correct FlatCurry application it is necessary
to define the number of arguments as the arity value (instead of
using the arity computed from the type). For this reason the compiler
needs a table containing the information for all known functions
and constructors. 
\begin{verbatim}

> type ArityEnv = TopEnv ArityInfo

> data ArityInfo = ArityInfo QualIdent Int deriving Show

> instance Entity ArityInfo where
>   origName (ArityInfo origName _) = origName

> bindArity :: ModuleIdent -> Ident -> Int -> ArityEnv -> ArityEnv
> bindArity mid id arity aEnv
>    | uniqueId id == 0 
>      = bindTopEnv "Base.bindArity" id arityInfo 
>                   (qualBindTopEnv "Base.bindArity" qid arityInfo aEnv)
>    | otherwise        
>      = bindTopEnv "Base.bindArity" id arityInfo aEnv
>  where
>  qid = qualifyWith mid id
>  arityInfo = ArityInfo qid arity

> lookupArity :: Ident -> ArityEnv -> [ArityInfo]
> lookupArity id aEnv = lookupTopEnv id aEnv ++! lookupTupleArity id

> qualLookupArity :: QualIdent -> ArityEnv -> [ArityInfo]
> qualLookupArity qid aEnv = qualLookupTopEnv qid aEnv
>		             ++! qualLookupConsArity qid aEnv
>			     ++! lookupTupleArity (unqualify qid)

> qualLookupConsArity :: QualIdent -> ArityEnv -> [ArityInfo]
> qualLookupConsArity qid aEnv
>    | (maybe False ((==) preludeMIdent) mmid) && (id == consId)
>      = qualLookupTopEnv (qualify id) aEnv
>    | otherwise
>      = []
>  where (mmid, id) = splitQualIdent qid

> lookupTupleArity :: Ident -> [ArityInfo]
> lookupTupleArity id 
>    | isTupleId id 
>      = [ArityInfo (qualifyWith preludeMIdent id) (tupleArity id)]
>    | otherwise
>      = []

\end{verbatim}
\paragraph{Module alias}
\begin{verbatim}

> type ImportEnv = Env ModuleIdent ModuleIdent

> bindAlias :: Decl -> ImportEnv -> ImportEnv
> bindAlias (ImportDecl _ mid _ mmid _) iEnv
>    = bindEnv mid (fromMaybe mid mmid) iEnv

> lookupAlias :: ModuleIdent -> ImportEnv -> Maybe ModuleIdent
> lookupAlias = lookupEnv

> sureLookupAlias :: ModuleIdent -> ImportEnv -> ModuleIdent
> sureLookupAlias m iEnv = fromMaybe m (lookupAlias m iEnv)


\end{verbatim}
\paragraph{Operator precedences}
In order to parse infix expressions correctly, the compiler must know
the precedence and fixity of each operator. Operator precedences are
associated with entities and will be checked after renaming was
applied. Nevertheless, we need to save precedences for ambiguous names
in order to handle them correctly while computing the exported
interface of a module.

If no fixity is assigned to an operator, it will be given the default
precedence 9 and assumed to be a left-associative operator.

\em{Note:} this modified version uses Haskell type \texttt{Integer}
for representing the precedence. This change had to be done due to the
introduction of unlimited integer constants in the parser / lexer.
\begin{verbatim}

> data OpPrec = OpPrec Infix Integer deriving Eq

> instance Show OpPrec where
>   showsPrec _ (OpPrec fix p) = showString (assoc fix) . shows p
>     where assoc InfixL = "left "
>           assoc InfixR = "right "
>           assoc Infix  = "non-assoc "

> defaultP :: OpPrec
> defaultP = OpPrec InfixL 9

\end{verbatim}
The lookup functions for the environment which maintains the operator
precedences are simpler than for the type and value environments
because they do not need to handle tuple constructors.
\begin{verbatim}

> data PrecInfo = PrecInfo QualIdent OpPrec deriving (Eq,Show)

> instance Entity PrecInfo where
>   origName (PrecInfo op _) = op

> type PEnv = TopEnv PrecInfo

> bindP :: ModuleIdent -> Ident -> OpPrec -> PEnv -> PEnv
> bindP m op p
>   | uniqueId op == 0 
>     = bindTopEnv "Base.bindP" op info . qualBindTopEnv "Base.bindP" op' info
>   | otherwise = bindTopEnv "Base.bindP" op info
>   where op' = qualifyWith m op
>         info = PrecInfo op' p

> lookupP :: Ident -> PEnv -> [PrecInfo]
> lookupP = lookupTopEnv

> qualLookupP :: QualIdent -> PEnv -> [PrecInfo]
> qualLookupP = qualLookupTopEnv

\end{verbatim}
\paragraph{Evaluation modes}
The compiler has to collect the evaluation annotations for a program
in an environment. As these annotations affect only local declarations,
a flat environment mapping unqualified names onto annotations is
sufficient.
\begin{verbatim}

> type EvalEnv = Env Ident EvalAnnotation

> bindEval :: Ident -> EvalAnnotation -> EvalEnv -> EvalEnv
> bindEval = bindEnv

> lookupEval :: Ident -> EvalEnv -> Maybe EvalAnnotation
> lookupEval f evEnv = lookupEnv f evEnv

\end{verbatim}
\paragraph{Predefined types}
The list and unit data types must be predefined because their
definitions
\begin{verbatim}
data () = ()
data [] a = [] | a : [a]
\end{verbatim}
are not allowed by Curry's syntax. The corresponding types
are available in the environments \texttt{initTCEnv} and
\texttt{initDCEnv}. In addition, the precedence of the (infix) list
constructor is available in the environment \texttt{initPEnv}.

Note that only the unqualified names are predefined. This is correct,
because neither \texttt{Prelude.()} nor \texttt{Prelude.[]} are valid
identifiers.
\begin{verbatim}

> initPEnv :: PEnv
> initPEnv =
>   predefTopEnv qConsId (PrecInfo qConsId (OpPrec InfixR 5)) emptyTopEnv

> initTCEnv :: TCEnv
> initTCEnv = foldr (uncurry predefTC) emptyTopEnv predefTypes
>   where a = typeVar 0
>         predefTC (TypeConstructor tc tys) cs =
>           predefTopEnv (qualify (unqualify tc))
>                        (DataType tc (length tys) (map Just cs))

> initDCEnv :: ValueEnv
> initDCEnv =
>   foldr (uncurry predefDC) emptyTopEnv
>         [(c,constrType (polyType ty) n' tys)
>         | (ty,cs) <- predefTypes, Data c n' tys <- cs]
>   where primTypes = map snd (moduleImports preludeMIdent initTCEnv)
>         predefDC c ty = predefTopEnv c' (DataConstructor c' ty)
>           where c' = qualify c
>         constrType (ForAll n ty) n' = ForAllExist n n' . foldr TypeArrow ty

> initAEnv :: ArityEnv
> initAEnv
>    = foldr bindPredefArity emptyTopEnv (concatMap snd predefTypes)
>  where
>  bindPredefArity (Data id _ ts) aEnv
>     = bindArity preludeMIdent id (length ts) aEnv

> initIEnv :: ImportEnv
> initIEnv = emptyEnv

> predefTypes :: [(Type,[Data [Type]])]
> predefTypes =
>   let a = typeVar 0 in [
>     (unitType,   [Data unitId 0 []]),
>     (listType a, [Data nilId 0 [],Data consId 0 [a,listType a]])
>   ]


\end{verbatim}
\paragraph{Free and bound variables}
The compiler needs to compute the sets of free and bound variables for
various different entities. We will devote three type classes to that
purpose. The \texttt{QualExpr} class is expected to take into account
that it is possible to use a qualified name to refer to a function
defined in the current module and therefore \emph{M.x} and $x$, where
$M$ is the current module name, should be considered the same name.
However note that this is correct only after renaming all local
definitions as \emph{M.x} always denotes an entity defined at the
top-level.

The \texttt{Decl} instance of \texttt{QualExpr} returns all free
variables on the right hand side, regardless of whether they are bound
on the left hand side. This is more convenient as declarations are
usually processed in a declaration group where the set of free
variables cannot be computed independently for each declaration. Also
note that the operator in a unary minus expression is not a free
variable. This operator always refers to a global function from the
prelude.
\begin{verbatim}

> class Expr e where
>   fv :: e -> [Ident]
> class QualExpr e where
>   qfv :: ModuleIdent -> e -> [Ident]
> class QuantExpr e where
>   bv :: e -> [Ident]

> instance Expr e => Expr [e] where
>   fv = concat . map fv
> instance QualExpr e => QualExpr [e] where
>   qfv m = concat . map (qfv m)
> instance QuantExpr e => QuantExpr [e] where
>   bv = concat . map bv

> instance QualExpr Decl where
>   qfv m (FunctionDecl _ _ eqs) = qfv m eqs
>   qfv m (PatternDecl _ _ rhs) = qfv m rhs
>   qfv _ _ = []

> instance QuantExpr Decl where
>   bv (TypeSig _ vs _) = vs
>   bv (EvalAnnot _ fs _) = fs
>   bv (FunctionDecl _ f _) = [f]
>   bv (ExternalDecl _ _ _ f _) = [f]
>   bv (FlatExternalDecl _ fs) = fs
>   bv (PatternDecl _ t _) = bv t
>   bv (ExtraVariables _ vs) = vs
>   bv _ = []

> instance QualExpr Equation where
>   qfv m (Equation _ lhs rhs) = filterBv lhs (qfv m lhs ++ qfv m rhs)

> instance QuantExpr Lhs where
>   bv = bv . snd . flatLhs

> instance QualExpr Lhs where
>   qfv m lhs = qfv m (snd (flatLhs lhs))

> instance QualExpr Rhs where
>   qfv m (SimpleRhs _ e ds) = filterBv ds (qfv m e ++ qfv m ds)
>   qfv m (GuardedRhs es ds) = filterBv ds (qfv m es ++ qfv m ds)

> instance QualExpr CondExpr where
>   qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

> instance QualExpr Expression where
>   qfv _ (Literal _) = []
>   qfv m (Variable v) = maybe [] return (localIdent m v)
>   qfv _ (Constructor _) = []
>   qfv m (Paren e) = qfv m e
>   qfv m (Typed e _) = qfv m e
>   qfv m (Tuple _ es) = qfv m es
>   qfv m (List _ es) = qfv m es
>   qfv m (ListCompr _ e qs) = foldr (qfvStmt m) (qfv m e) qs
>   qfv m (EnumFrom e) = qfv m e
>   qfv m (EnumFromThen e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromTo e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (UnaryMinus _ e) = qfv m e
>   qfv m (Apply e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (InfixApply e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
>   qfv m (LeftSection e op) = qfv m op ++ qfv m e
>   qfv m (RightSection op e) = qfv m op ++ qfv m e
>   qfv m (Lambda _ ts e) = filterBv ts (qfv m e)
>   qfv m (Let ds e) = filterBv ds (qfv m ds ++ qfv m e)
>   qfv m (Do sts e) = foldr (qfvStmt m) (qfv m e) sts
>   qfv m (IfThenElse _ e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (Case _ e alts) = qfv m e ++ qfv m alts
>   qfv m (RecordConstr fs) = qfv m fs
>   qfv m (RecordSelection e _) = qfv m e
>   qfv m (RecordUpdate fs e) = qfv m e ++ qfv m fs

> qfvStmt :: ModuleIdent -> Statement -> [Ident] -> [Ident]
> qfvStmt m st fvs = qfv m st ++ filterBv st fvs

> instance QualExpr Statement where
>   qfv m (StmtExpr _ e) = qfv m e
>   qfv m (StmtDecl ds) = filterBv ds (qfv m ds)
>   qfv m (StmtBind _ t e) = qfv m e

> instance QualExpr Alt where
>   qfv m (Alt _ t rhs) = filterBv t (qfv m rhs)

> instance QuantExpr a => QuantExpr (Field a) where
>   bv (Field _ _ t) = bv t

> instance QualExpr a => QualExpr (Field a) where
>   qfv m (Field _ _ t) = qfv m t

> instance QuantExpr Statement where
>   bv (StmtExpr _ e) = []
>   bv (StmtBind _ t e) = bv t
>   bv (StmtDecl ds) = bv ds

> instance QualExpr InfixOp where
>   qfv m (InfixOp op) = qfv m (Variable op)
>   qfv _ (InfixConstr _) = []

> instance QuantExpr ConstrTerm where
>   bv (LiteralPattern _) = []
>   bv (NegativePattern _ _) = []
>   bv (VariablePattern v) = [v]
>   bv (ConstructorPattern c ts) = bv ts
>   bv (InfixPattern t1 op t2) = bv t1 ++ bv t2
>   bv (ParenPattern t) = bv t
>   bv (TuplePattern _ ts) = bv ts
>   bv (ListPattern _ ts) = bv ts
>   bv (AsPattern v t) = v : bv t
>   bv (LazyPattern _ t) = bv t
>   bv (FunctionPattern f ts) = bvFuncPatt (FunctionPattern f ts)
>   bv (InfixFuncPattern t1 op t2) = bvFuncPatt (InfixFuncPattern t1 op t2)
>   bv (RecordPattern fs r) = (maybe [] bv r) ++ bv fs

> instance QualExpr ConstrTerm where
>   qfv _ (LiteralPattern _) = []
>   qfv _ (NegativePattern _ _) = []
>   qfv _ (VariablePattern _) = []
>   qfv m (ConstructorPattern _ ts) = qfv m ts
>   qfv m (InfixPattern t1 _ t2) = qfv m [t1,t2]
>   qfv m (ParenPattern t) = qfv m t
>   qfv m (TuplePattern _ ts) = qfv m ts
>   qfv m (ListPattern _ ts) = qfv m ts
>   qfv m (AsPattern _ ts) = qfv m ts
>   qfv m (LazyPattern _ t) = qfv m t
>   qfv m (FunctionPattern f ts) 
>     = (maybe [] return (localIdent m f)) ++ qfv m ts
>   qfv m (InfixFuncPattern t1 op t2) 
>     = (maybe [] return (localIdent m op)) ++ qfv m [t1,t2]
>   qfv m (RecordPattern fs r) = (maybe [] (qfv m) r) ++ qfv m fs

> instance Expr TypeExpr where
>   fv (ConstructorType _ tys) = fv tys
>   fv (VariableType tv)
>     | tv == anonId = []
>     | otherwise = [tv]
>   fv (TupleType tys) = fv tys
>   fv (ListType ty) = fv ty
>   fv (ArrowType ty1 ty2) = fv ty1 ++ fv ty2
>   fv (RecordType fs rty) = (maybe [] fv rty) ++ fv (map snd fs)

> filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
> filterBv e = filter (`notElemSet` fromListSet (bv e))

\end{verbatim}
Since multiple variable occurrences are allowed in function patterns,
it is necessary to compute the list of bound variables in a different way:
Each variable occuring in the function pattern will be unique in the result
list.
\begin{verbatim}

> bvFuncPatt :: ConstrTerm -> [Ident]
> bvFuncPatt = bvfp []
>  where
>  bvfp bvs (LiteralPattern _) = bvs
>  bvfp bvs (NegativePattern _ _) = bvs
>  bvfp bvs (VariablePattern v)
>     | elem v bvs = bvs
>     | otherwise  = v:bvs
>  bvfp bvs (ConstructorPattern c ts) = foldl bvfp bvs ts
>  bvfp bvs (InfixPattern t1 op t2) = foldl bvfp bvs [t1,t2]
>  bvfp bvs (ParenPattern t) = bvfp bvs t
>  bvfp bvs (TuplePattern _ ts) = foldl bvfp bvs ts
>  bvfp bvs (ListPattern _ ts) = foldl bvfp bvs ts
>  bvfp bvs (AsPattern v t)
>     | elem v bvs = bvfp bvs t
>     | otherwise  = bvfp (v:bvs) t
>  bvfp bvs (LazyPattern _ t) = bvfp bvs t
>  bvfp bvs (FunctionPattern f ts) = foldl bvfp bvs ts
>  bvfp bvs (InfixFuncPattern t1 op t2) = foldl bvfp bvs [t1, t2]
>  bvfp bvs (RecordPattern fs r)
>     = foldl bvfp (maybe bvs (bvfp bvs) r) (map fieldTerm fs)

\end{verbatim}
\paragraph{Miscellany}
Error handling
\begin{verbatim}

> errorAt :: Position -> String -> a
> errorAt p msg = error ("\n" ++ show p ++ ": " ++ msg)

> errorAt' :: (Position,String) -> a
> errorAt' = uncurry errorAt

> internalError :: String -> a
> internalError what = error ("internal error: " ++ what)

\end{verbatim}
Name supply for the generation of (type) variable names.
\begin{verbatim}

> nameSupply :: [Ident]
> nameSupply = map mkIdent [c:showNum i | i <- [0..], c <- ['a'..'z']]
>   where showNum 0 = ""
>         showNum n = show n

\end{verbatim}
\ToDo{The \texttt{nameSupply} should respect the current case mode, 
i.e., use upper case for variables in Prolog mode.}

Here is a list of predicates identifying various kinds of
declarations.
\begin{verbatim}

> isImportDecl, isInfixDecl, isTypeDecl :: Decl -> Bool
> isTypeSig, isEvalAnnot, isExtraVariables, isValueDecl :: Decl -> Bool
> isImportDecl (ImportDecl _ _ _ _ _) = True
> isImportDecl _ = False
> isInfixDecl (InfixDecl _ _ _ _) = True
> isInfixDecl _ = False
> isTypeDecl (DataDecl _ _ _ _) = True
> isTypeDecl (NewtypeDecl _ _ _ _) = True
> isTypeDecl (TypeDecl _ _ _ _) = True
> isTypeDecl _ = False
> isTypeSig (TypeSig _ _ _) = True
> isTypeSig (ExternalDecl _ _ _ _ _) = True
> isTypeSig _ = False
> isEvalAnnot (EvalAnnot _ _ _) = True
> isEvalAnnot _ = False
> isExtraVariables (ExtraVariables _ _) = True
> isExtraVariables _ = False
> isValueDecl (FunctionDecl _ _ _) = True
> isValueDecl (ExternalDecl _ _ _ _ _) = True
> isValueDecl (FlatExternalDecl _ _) = True
> isValueDecl (PatternDecl _ _ _) = True
> isValueDecl (ExtraVariables _ _) = True
> isValueDecl _ = False
> isRecordDecl (TypeDecl _ _ _ (RecordType _ _)) = True
> isRecordDecl _ = False

> isIImportDecl :: IDecl -> Bool
> isIImportDecl (IImportDecl _ _) = True
> isIImportDecl _ = False

\end{verbatim}
The function \texttt{infixOp} converts an infix operator into an
expression.
\begin{verbatim}

> infixOp :: InfixOp -> Expression
> infixOp (InfixOp op) = Variable op
> infixOp (InfixConstr op) = Constructor op

\end{verbatim}
The function \texttt{linear} checks whether a list of entities is
linear, i.e., if every entity in the list occurs only once. If it is
non-linear, the first offending object is returned.
\begin{verbatim}

> data Linear a = Linear | NonLinear a

> linear :: Eq a => [a] -> Linear a
> linear (x:xs)
>   | x `elem` xs = NonLinear x
>   | otherwise = linear xs
> linear [] = Linear

\end{verbatim}
In order to give precise error messages on duplicate definitions of
identifiers, the compiler pairs identifiers with their position in the
source file when passing them to the function above. However, the
position must be ignored when comparing two such pairs.
\begin{verbatim}

> data PIdent = PIdent Position Ident

> instance Eq PIdent where
>   PIdent _ x == PIdent _ y = x == y

\end{verbatim}





