% -*- LaTeX -*-
% $Id: Types.lhs,v 1.11 2004/02/08 22:14:02 wlux Exp $
%
% Copyright (c) 2002, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Types.lhs}
\section{Types}
This module modules provides the definitions for the internal 
representation of types in the compiler.
\begin{verbatim}

> module Types where
> import Ident
> import List

\end{verbatim}
A type is either a type variable, an application of a type constructor
to a list of arguments, or an arrow type. The \texttt{TypeConstrained}
case is used for representing type variables that are restricted to a
particular set of types. At present, this is used for typing guard
expressions, which are restricted to be either of type \texttt{Bool}
or of type \texttt{Success}, and integer literals, which are
restricted to types \texttt{Int} and \texttt{Float}. If the type is
not restricted it defaults to the first type from the constraint list.
The case \texttt{TypeSkolem} is used for handling skolem types, which
result from the use of existentially quantified data constructors.

Type variables are represented with deBruijn style indices. Universally
quantified type variables are assigned indices in the order of their
occurrence in the type from left to right. This leads to a canonical
representation of types where $\alpha$-equivalence of two types
coincides with equality of the representation.

Note that even though \texttt{TypeConstrained} variables use indices
as well, these variables must never be quantified.
\begin{verbatim}

> data Type =
>     TypeConstructor QualIdent [Type]
>   | TypeVariable Int
>   | TypeConstrained [Type] Int
>   | TypeArrow Type Type
>   | TypeSkolem Int
>   deriving (Eq,Show)

\end{verbatim}
The function \texttt{isArrowType} checks whether a type is a function
type $t_1 \rightarrow t_2 \rightarrow \dots \rightarrow t_n$ . The
function \texttt{arrowArity} computes the arity $n$ of a function type
and \texttt{arrowBase} returns the type $t_n$.
\begin{verbatim}

> isArrowType :: Type -> Bool
> isArrowType (TypeArrow _ _) = True
> isArrowType _ = False

> arrowArity :: Type -> Int
> arrowArity (TypeArrow _ ty) = 1 + arrowArity ty
> arrowArity _ = 0

> arrowArgs :: Type -> [Type]
> arrowArgs (TypeArrow ty1 ty2) = ty1 : arrowArgs ty2
> arrowArgs ty = []

> arrowBase :: Type -> Type
> arrowBase (TypeArrow _ ty) = arrowBase ty
> arrowBase ty = ty

\end{verbatim}
The functions \texttt{typeVars}, \texttt{typeConstrs},
\texttt{typeSkolems} return a list of all type variables, type
constructors, or skolems occurring in a type $t$, respectively. Note
that \texttt{TypeConstrained} variables are not included in the set of
type variables because they cannot be generalized.
\begin{verbatim}

> typeVars :: Type -> [Int]
> typeVars ty = vars ty []
>   where vars (TypeConstructor _ tys) tvs = foldr vars tvs tys
>         vars (TypeVariable tv) tvs = tv : tvs
>         vars (TypeConstrained _ _) tvs = tvs
>         vars (TypeArrow ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
>         vars (TypeSkolem _) tvs = tvs

> typeConstrs :: Type -> [QualIdent]
> typeConstrs ty = types ty []
>   where types (TypeConstructor tc tys) tcs = tc : foldr types tcs tys
>         types (TypeVariable _) tcs = tcs
>         types (TypeConstrained _ _) tcs = tcs
>         types (TypeArrow ty1 ty2) tcs = types ty1 (types ty2 tcs)
>         types (TypeSkolem _) tcs = tcs

> typeSkolems :: Type -> [Int]
> typeSkolems ty = skolems ty []
>   where skolems (TypeConstructor _ tys) sks = foldr skolems sks tys
>         skolems (TypeVariable _) sks = sks
>         skolems (TypeConstrained _ _) sks = sks
>         skolems (TypeArrow ty1 ty2) sks = skolems ty1 (skolems ty2 sks)
>         skolems (TypeSkolem k) sks = k : sks

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

> data TypeScheme = ForAll Int Type deriving (Eq,Show)
> data ExistTypeScheme = ForAllExist Int Int Type deriving (Eq,Show)

\end{verbatim}
The functions \texttt{monoType} and \texttt{polyType} translate a type
$\tau$ into a monomorphic type scheme $\forall.\tau$ and a polymorphic
type scheme $\forall\overline{\alpha}.\tau$ where $\overline{\alpha} =
\textrm{fv}(\tau)$, respectively. \texttt{polyType} assumes that all
universally quantified variables in the type are assigned indices
starting with 0 and does not renumber the variables.
\begin{verbatim}

> monoType, polyType :: Type -> TypeScheme
> monoType ty = ForAll 0 ty
> polyType ty = ForAll (maximum (-1 : typeVars ty) + 1) ty

\end{verbatim}
There are a few predefined types:
\begin{verbatim}

> unitType,boolType,charType,intType,floatType,stringType,successType :: Type
> unitType = primType unitId []
> boolType = primType boolId []
> charType = primType charId []
> intType = primType intId []
> floatType = primType floatId []
> stringType = listType charType
> successType = primType successId []

> listType,ioType :: Type -> Type
> listType ty = primType listId [ty]
> ioType ty = primType ioId [ty]

> tupleType :: [Type] -> Type
> tupleType tys = primType (tupleId (length tys)) tys

> primType :: Ident -> [Type] -> Type
> primType = TypeConstructor . qualifyWith preludeMIdent

> typeVar :: Int -> Type
> typeVar = TypeVariable

\end{verbatim}
