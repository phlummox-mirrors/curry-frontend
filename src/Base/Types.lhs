% $Id: Types.lhs,v 1.11 2004/02/08 22:14:02 wlux Exp $
%
% Copyright (c) 2002-2004, Wolfgang Lux
%                    2013, Matthias Böhm
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{Types.lhs}
\section{Types}
This module modules provides the definitions for the internal
representation of types in the compiler.
\begin{verbatim}

TODO: Use MultiParamTypeClasses ?

> {-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

> module Base.Types
>   ( -- * Representation of Types
>     Type (..), isArrowType, arrowArity, arrowArgs, arrowBase, typeVars
>   , typeConstrs, typeSkolems, equTypes, qualifyType, unqualifyType
>   , qualifyContext, qualifyConstrType, unqualifyContext
>     -- * Representation of Data Constructors
>   , DataConstr (..), constrIdent, tupleData
>     -- * Representation of Quantification
>   , TypeScheme (..), ExistTypeScheme (..), monoType, monoType', polyType
>   , typeSchemeToType
>     -- * Type classes context represenatations
>   , emptyContext, Context, constrainBy, mkContext, combineContext
>   , getContext
>     -- * Predefined types
>   , unitType, boolType, charType, intType, floatType, stringType
>   , successType, listType, ioType, tupleType 
>   , typeVar, predefTypes
>     -- * Helper functions
>   , isTyCons, isArrow, isCons, splitType
>    -- * Mirror functions
>   , Mirrorable (..)
>   ) where

> import Curry.Base.Ident
> import Text.PrettyPrint
> import Curry.Syntax.Pretty hiding (ppContext)
> import qualified Curry.Syntax.Type as ST

\end{verbatim}
A type is either a type variable, an application of a type constructor
to a list of arguments, or an arrow type. The \texttt{TypeConstrained}
case is used for representing type variables that are restricted to a
particular set of types. At present, this is used for typing guard
expressions, which are restricted to be either of type \texttt{Bool}
or of type \texttt{Success}, and integer literals, which are
restricted to types \texttt{Int} and \texttt{Float}. If the type is
not restricted, it defaults to the first type from the constraint list.
The case \texttt{TypeSkolem} is used for handling skolem types, which
result from the use of existentially quantified data constructors.
Finally, \texttt{TypeRecord} is used for records.

Type variables are represented with deBruijn style indices. Universally
quantified type variables are assigned indices in the order of their
occurrence in the type from left to right. This leads to a canonical
representation of types where $\alpha$-equivalence of two types
coincides with equality of the representation.

Note that even though \texttt{TypeConstrained} variables use indices
as well, these variables must never be quantified.
\begin{verbatim}

> data Type
>   = TypeVariable Int
>   | TypeConstructor QualIdent [Type]
>   | TypeArrow Type Type
>   | TypeConstrained [Type] Int
>   | TypeSkolem Int
>   | TypeRecord [(Ident, Type)] (Maybe Int)
>   deriving (Eq, Ord)

> isTyCons :: Type -> Bool
> isTyCons (TypeConstructor _     _) = True
> isTyCons (TypeConstrained (t:_) _) = isTyCons t
> isTyCons (TypeConstrained []    _) = False
> isTyCons _                         = False

> isArrow :: Type -> Bool
> isArrow (TypeArrow _ _) = True
> isArrow _               = False

> -- | returns whether the given type is a constructor type, i.e. whether its head is
> -- a constructor
> isCons :: Type -> Bool
> isCons t = isTyCons t || isArrow t

> -- |splits a given type (that starts with a constructor) into
> -- the constructor and its following types 
> splitType :: Type -> Maybe (QualIdent, [Type])
> splitType (TypeConstructor  xi tys) = Just (xi, tys)
> splitType (TypeArrow       ty1 ty2) = Just (qArrowIdP, [ty1, ty2])
> splitType (TypeConstrained (t:_) _) = splitType t
> splitType (TypeConstrained    [] _) = Nothing
> splitType _                         = Nothing

\end{verbatim}
The function \texttt{isArrowType} checks whether a type is a function
type $t_1 \rightarrow t_2 \rightarrow \dots \rightarrow t_n$ . The
function \texttt{arrowArity} computes the arity $n$ of a function type,
\texttt{arrowArgs} computes the types $t_1 \dots t_{n-1}$
and \texttt{arrowBase} returns the type $t_n$.
\begin{verbatim}

> isArrowType :: Type -> Bool
> isArrowType (TypeArrow _ _) = True
> isArrowType _               = False

> arrowArity :: Type -> Int
> arrowArity (TypeArrow _ ty) = 1 + arrowArity ty
> arrowArity _                = 0

> arrowArgs :: Type -> [Type]
> arrowArgs (TypeArrow ty1 ty2) = ty1 : arrowArgs ty2
> arrowArgs _                   = []

> arrowBase :: Type -> Type
> arrowBase (TypeArrow _ ty) = arrowBase ty
> arrowBase ty               = ty

\end{verbatim}
The functions \texttt{typeVars}, \texttt{typeConstrs},
\texttt{typeSkolems} return a list of all type variables, type
constructors, or skolems occurring in a type $t$, respectively. Note
that \texttt{TypeConstrained} variables are not included in the set of
type variables because they cannot be generalized.
\begin{verbatim}

> typeVars :: Type -> [Int]
> typeVars ty = vars ty [] where
>   vars (TypeConstructor _ tys) tvs = foldr vars tvs tys
>   vars (TypeVariable       tv) tvs = tv : tvs
>   vars (TypeConstrained   _ _) tvs = tvs
>   vars (TypeArrow     ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
>   vars (TypeSkolem          _) tvs = tvs
>   vars (TypeRecord     fs rtv) tvs =
>     foldr vars (maybe tvs (:tvs) rtv) (map snd fs)

> typeConstrs :: Type -> [QualIdent]
> typeConstrs ty = constrs ty [] where
>   constrs (TypeConstructor tc tys) tcs = tc : foldr constrs tcs tys
>   constrs (TypeVariable         _) tcs = tcs
>   constrs (TypeConstrained    _ _) tcs = tcs
>   constrs (TypeArrow      ty1 ty2) tcs = constrs ty1 (constrs ty2 tcs)
>   constrs (TypeSkolem           _) tcs = tcs
>   constrs (TypeRecord        fs _) tcs = foldr constrs tcs (map snd fs)

> typeSkolems :: Type -> [Int]
> typeSkolems ty = skolems ty [] where
>   skolems (TypeConstructor _ tys) sks = foldr skolems sks tys
>   skolems (TypeVariable        _) sks = sks
>   skolems (TypeConstrained   _ _) sks = sks
>   skolems (TypeArrow     ty1 ty2) sks = skolems ty1 (skolems ty2 sks)
>   skolems (TypeSkolem          k) sks = k : sks
>   skolems (TypeRecord       fs _) sks = foldr skolems sks (map snd fs)

\end{verbatim}
The function \texttt{equTypes} computes whether two types are equal modulo
renaming of type variables.
\begin{verbatim}

> equTypes :: Type -> Type -> Bool
> equTypes t1 t2 = fst (equ [] t1 t2)
>  where
>  -- @is@ is an AssocList of type variable indices
>  equ is (TypeConstructor qid1 ts1) (TypeConstructor qid2 ts2)
>    | qid1 == qid2 = equs is ts1 ts2
>    | otherwise    = (False, is)
>  equ is (TypeVariable          i1) (TypeVariable          i2)
>    = equVar is i1 i2
>  equ is (TypeConstrained   ts1 i1) (TypeConstrained   ts2 i2)
>    = let (res , is1) = equs   is  ts1 ts2
>          (res2, is2) = equVar is1 i1  i2
>      in  (res && res2, is2)
>  equ is (TypeArrow        tf1 tt1) (TypeArrow        tf2 tt2)
>    = let (res1, is1) = equ is  tf1 tf2
>          (res2, is2) = equ is1 tt1 tt2
>      in  (res1 && res2, is2)
>  equ is (TypeSkolem            i1) (TypeSkolem            i2)
>   = equVar is i1 i2
>  equ is (TypeRecord fs1 (Just r1)) (TypeRecord fs2 (Just r2))
>    = let (res1, is1) = equVar     is  r1  r2
>          (res2, is2) = equRecords is1 fs1 fs2
>      in  (res1 && res2, is2)
>  equ is (TypeRecord fs1   Nothing) (TypeRecord fs2   Nothing)
>    = equRecords is fs1 fs2
>  equ is _                         _
>    = (False, is)
>
>  equVar is i1 i2 = case lookup i1 is of
>    Nothing  -> (True, (i1, i2) : is)
>    Just i2' -> (i2 == i2', is)
>
>  equRecords is fs1 fs2 | length fs1 == length fs2 = equrec is fs1 fs2
>                        | otherwise                = (False, is)
>
>  equrec is []               _   = (True, is)
>  equrec is ((l1, ty1) : fs1) fs2
>    = let (res1, is1) = maybe (False, is) (equ is ty1) (lookup l1 fs2)
>          (res2, is2) = equrec is1 fs1 fs2
>      in  (res1 && res2, is2)
>
>  equs is []        []        = (True , is)
>  equs is (t1':ts1) (t2':ts2)
>     = let (res1, is1) = equ  is t1'  t2'
>           (res2, is2) = equs is1 ts1 ts2
>       in  (res1 && res2, is2)
>  equs is _         _         = (False, is)

\end{verbatim}
The functions \texttt{qualifyType} and \texttt{unqualifyType} add/remove the
qualification with a module identifier for type constructors.
\begin{verbatim}

> qualifyType :: ModuleIdent -> Type -> Type
> qualifyType m (TypeConstructor tc tys)
>   | isTupleId tc'           = tupleType tys'
>   | tc' == unitId && n == 0 = unitType
>   | tc' == listId && n == 1 = listType (head tys')
>   | otherwise = TypeConstructor (qualQualify m tc) tys'
>   where n    = length tys'
>         tc'  = unqualify tc
>         tys' = map (qualifyType m) tys
> qualifyType _ var@(TypeVariable     _) = var
> qualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (qualifyType m) tys) tv
> qualifyType m (TypeArrow      ty1 ty2) =
>   TypeArrow (qualifyType m ty1) (qualifyType m ty2)
> qualifyType _ skol@(TypeSkolem      _) = skol
> qualifyType m (TypeRecord      fs rty) =
>   TypeRecord (map (\ (l, ty) -> (l, qualifyType m ty)) fs) rty

> unqualifyType :: ModuleIdent -> Type -> Type
> unqualifyType m (TypeConstructor tc tys) =
>   TypeConstructor (qualUnqualify m tc) (map (unqualifyType m) tys)
> unqualifyType _ var@(TypeVariable     _) = var
> unqualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (unqualifyType m) tys) tv
> unqualifyType m (TypeArrow      ty1 ty2) =
>   TypeArrow (unqualifyType m ty1) (unqualifyType m ty2)
> unqualifyType _ skol@(TypeSkolem      _) = skol
> unqualifyType m (TypeRecord      fs rty) =
>   TypeRecord (map (\ (l, ty) -> (l, unqualifyType m ty)) fs) rty

> qualifyContext :: ModuleIdent -> Context -> Context
> qualifyContext m cx = map qualifyContext' cx
>   where
>   qualifyContext' :: (QualIdent, Type) -> (QualIdent, Type)
>   qualifyContext' (cls, ty) = (qualQualify m cls, qualifyType m ty)  

> qualifyConstrType :: ModuleIdent -> (Context, Type) -> (Context, Type)
> qualifyConstrType m (cx, ty) = (qualifyContext m cx, qualifyType m ty) 

> unqualifyContext :: ModuleIdent -> Context -> Context
> unqualifyContext m cx = map unqualifyContext' cx
>   where
>   unqualifyContext' :: (QualIdent, Type) -> (QualIdent, Type)
>   unqualifyContext' (cls, ty) = (qualUnqualify m cls, unqualifyType m ty)

\end{verbatim}
The type \texttt{Data} is used to represent value constructors introduced
by data or newtype declarations.
\begin{verbatim}

> data DataConstr = DataConstr Ident Int [Type]
>     deriving (Eq, Show)

> constrIdent :: DataConstr -> Ident
> constrIdent (DataConstr c _ _) = c

\end{verbatim}
We support two kinds of quantifications of types here, universally
quantified type schemes $\forall\overline{\alpha} .
\tau(\overline{\alpha})$ and universally and existentially quantified
type schemes $\forall\overline{\alpha} \exists\overline{\eta} .
\tau(\overline{\alpha},\overline{\eta})$.  In both, quantified type
variables are assigned ascending indices starting from 0. Therefore it
is sufficient to record the numbers of quantified type variables in
the \texttt{ForAll} and \texttt{ForAllExist} constructors. In case of
the latter, the first of the two numbers is the number of universally
quantified variables and the second the number of existentially
quantified variables.
\begin{verbatim}

> data TypeScheme = ForAll Context Int Type deriving Eq
> data ExistTypeScheme = ForAllExist Context Int Int Type deriving Eq

> typeSchemeToType :: TypeScheme -> Type
> typeSchemeToType (ForAll _ _ t) = t

> type Context = [(QualIdent, Type)]
 
> emptyContext :: Context
> emptyContext = []

> constrainBy :: TypeScheme -> Context -> TypeScheme
> constrainBy (ForAll _cx n t) cx = (ForAll cx n t) 

> combineContext :: Context -> TypeScheme -> TypeScheme
> combineContext cx (ForAll cx' n t) = ForAll (cx ++ cx') n t

> mkContext :: [(QualIdent, Type)] -> Context
> mkContext = id 

> getContext :: TypeScheme -> Context
> getContext (ForAll cx _ _) = cx

\end{verbatim}
The functions \texttt{monoType} and \texttt{polyType} translate a type
$\tau$ into a monomorphic type scheme $\forall.\tau$ and a polymorphic
type scheme $\forall\overline{\alpha}.\tau$ where $\overline{\alpha} =
\textrm{fv}(\tau)$, respectively. \texttt{polyType} assumes that all
universally quantified variables in the type are assigned indices
starting with 0 and does not renumber the variables.
\begin{verbatim}

> monoType :: Type -> TypeScheme
> monoType ty = ForAll emptyContext 0 ty

> polyType :: Type -> TypeScheme
> polyType ty = ForAll emptyContext (maximum (-1 : typeVars ty) + 1) ty

> monoType' :: (Context, Type) -> TypeScheme
> monoType' (cx, ty) = ForAll cx 0 ty 

\end{verbatim}
There are a few predefined types:
\begin{verbatim}

> unitType :: Type
> unitType = primType qUnitId []

> boolType :: Type
> boolType = primType qBoolId []

> charType :: Type
> charType = primType qCharId []

> intType :: Type
> intType = primType qIntId []

> floatType :: Type
> floatType = primType qFloatId []

> stringType :: Type
> stringType = listType charType

> successType :: Type
> successType = primType qSuccessId []

> listType :: Type -> Type
> listType ty = primType qListId [ty]

> ioType :: Type -> Type
> ioType ty = primType qIOId [ty]

> tupleType :: [Type] -> Type
> tupleType tys = primType (qTupleId (length tys)) tys

> typeVar :: Int -> Type
> typeVar = TypeVariable

> primType :: QualIdent -> [Type] -> Type
> primType = TypeConstructor --  . qualifyWith preludeMIdent

> predefTypes :: [(Type, [DataConstr])]
> predefTypes = let a = typeVar 0 in
>   [ (unitType  , [ DataConstr unitId 0 [] ])
>   , (listType a, [ DataConstr nilId  0 []
>                  , DataConstr consId 0 [a, listType a]
>                  ])
>   ]

> tupleData :: [DataConstr]
> tupleData = [DataConstr (tupleId n) n (take n tvs) | n <- [2 ..]]
>   where tvs = map typeVar [0 ..]

\end{verbatim}
Some pretty printing functions:
\begin{verbatim}

> instance Show TypeScheme where
>   show = show . ppTypeScheme

> instance Show ExistTypeScheme where
>   show = show . ppExistTypeScheme
  
> instance Show Type where
>   show = show . ppType


  
> ppTypeScheme :: TypeScheme -> Doc
> ppTypeScheme (ForAll cx n type0) = parens (text "ForAll" <+> text (show n) 
>   <+> ppContext cx <+> text "=>" <+> ppType type0)

> ppExistTypeScheme :: ExistTypeScheme -> Doc
> ppExistTypeScheme (ForAllExist cx n1 n2 type0) 
>   = parens (text "ForAllExist" <+> text (show n1) <+> text (show n2) 
>   <+> ppContext cx <+> text "=>" <+> ppType type0)

> ppContext :: Context -> Doc
> ppContext cx = parens $ hsep $ 
>   punctuate comma (map (\(qid, ty) -> ppQIdent qid <+> ppType ty) cx)

> ppType :: Type -> Doc
> ppType (TypeVariable n) = text (show n)
> ppType (TypeConstructor c ts) = 
>   (if length ts == 0 then id else parens) $ text (show c) <+> hsep (map ppType ts)
> ppType (TypeArrow t1 t2) = parens $ ppType t1 <+> text "->" <+> ppType t2
> ppType (TypeConstrained ts n) 
>   = text "constr" <> text (show n) <> parens (hsep (map ppType ts))
> ppType (TypeSkolem n) = text "skolem" <+> text (show n)
> ppType (TypeRecord r n) 
>   = text "record" <+> parens (text (show r) <+> text (show n))

\end{verbatim}
Functions for converting between the context/type data type used in curry-frontend
and the context/type data types used in curry-base. This mirroring is necessary
because we cannot have cyclic dependencies between two modules like curry-base
and curry-frontend, but in curry-base we *do* want to refer to the type datatypes
in curry-frontend, hence the mirroring. 

TODO: remove this functions as soon as possible

The functions are named by the following scheme: functions mirroring from
the frontend to base are named mirrorFB, functions mirroring from
the base to the frontend mirrorBF. 
\begin{verbatim}

> class Mirrorable a b where
>   mirrorFB :: a -> b
>   mirrorBF :: b -> a

> type ConstrType = (Context, Type)

> instance Mirrorable Context ST.Context_ where
>   mirrorFB cx = map (\(qid, ty) -> (qid, mirrorFB ty)) cx
>   mirrorBF cx = map (\(qid, ty) -> (qid, mirrorBF ty)) cx

> instance Mirrorable Type ST.Type_ where
>   mirrorFB (TypeVariable        n) = ST.TypeVariable_ n
>   mirrorFB (TypeConstructor q tys) = ST.TypeConstructor_ q (map mirrorFB tys)
>   mirrorFB (TypeArrow       t1 t2) = ST.TypeArrow_ (mirrorFB t1) (mirrorFB t2)
>   mirrorFB (TypeConstrained tys n) = ST.TypeConstrained_ (map mirrorFB tys) n
>   mirrorFB (TypeSkolem          n) = ST.TypeSkolem_ n
>   mirrorFB (TypeRecord      tys n) = 
>     ST.TypeRecord_ (map (\(id0, ty) -> (id0, mirrorFB ty)) tys) n
>   
>   mirrorBF (ST.TypeVariable_        n) = TypeVariable n
>   mirrorBF (ST.TypeConstructor_ q tys) = TypeConstructor q (map mirrorBF tys)
>   mirrorBF (ST.TypeArrow_       t1 t2) = TypeArrow (mirrorBF t1) (mirrorBF t2)
>   mirrorBF (ST.TypeConstrained_ tys n) = TypeConstrained (map mirrorBF tys) n
>   mirrorBF (ST.TypeSkolem_          n) = TypeSkolem n
>   mirrorBF (ST.TypeRecord_      tys n) = 
>     TypeRecord (map (\(id0, ty) -> (id0, mirrorBF ty)) tys) n

> instance Mirrorable ConstrType ST.ConstrType_ where
>   mirrorFB (cx, ty) = (mirrorFB cx, mirrorFB ty)
>   mirrorBF (cx, ty) = (mirrorBF cx, mirrorBF ty)


\end{verbatim}
