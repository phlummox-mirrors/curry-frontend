% -*- LaTeX -*-
% $Id: IntfSyntaxCheck.lhs 2148 2007-04-02 13:56:20Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Björn Peemöller (bjp@informatik.uni-kiel.de)
%
\nwfilename{IntfSyntaxCheck.lhs}
\section{Checking Interface Declarations}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler also checks that all type constructor
applications are saturated. Since interface files are closed -- i.e.,
they include declarations of all entities which are defined in other
modules -- the compiler can perform this check without reference to
the global environments.
\begin{verbatim}

> module Checks.InterfaceSyntaxCheck (intfSyntaxCheck) where

> import Control.Monad (liftM, liftM2, liftM3)
> import qualified Control.Monad.State as S
> import Data.List (nub, partition)
> import Data.Maybe (catMaybes)
> import Text.PrettyPrint

> import Base.Expr
> import Base.Messages (Message, posMessage, internalError)
> import Base.TopEnv
> import Base.Utils (findMultiples)
> import Env.TypeConstructor

> import Curry.Base.Ident
> import Curry.Syntax

import Base
import Error
import List
import Maybe
import Monad
import TopEnv

> data ISCState = ISCState
>   { typeEnv :: TypeEnv
>   , errors  :: [Message]
>   }

> type ISC = S.State ISCState

> getTypeEnv :: ISC TypeEnv
> getTypeEnv = S.gets typeEnv

> -- |Report a syntax error
> report :: Message -> ISC ()
> report msg = S.modify $ \ s -> s { errors = msg : errors s }

> intfSyntaxCheck :: Interface -> (Interface, [Message])
> intfSyntaxCheck (Interface n is ds) = (Interface n is ds', reverse $ errors s')
>   where (ds', s') = S.runState (mapM checkIDecl ds) (ISCState env [])
>         env = foldr bindType (fmap typeKind initTCEnv) ds

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in interfaces.
\begin{verbatim}

> bindType :: IDecl -> TypeEnv -> TypeEnv
> bindType (IInfixDecl       _ _ _ _) = id
> bindType (HidingDataDecl    _ tc _) = qualBindTopEnv "" tc (Data tc [])
> bindType (IDataDecl      _ tc _ cs) = qualBindTopEnv "" tc
>                                       (Data tc (map constr (catMaybes cs)))
>   where constr (ConstrDecl    _ _ c _) = c
>         constr (ConOpDecl  _ _ _ op _) = op
> bindType (INewtypeDecl   _ tc _ nc) = qualBindTopEnv "" tc (Data tc [nconstr nc])
>   where nconstr (NewConstrDecl _ _ c _) = c
> bindType (ITypeDecl       _ tc _ _) = qualBindTopEnv "" tc (Alias tc)
> bindType (IFunctionDecl  _ _ _ _ _) = id
> bindType (IClassDecl _ _ _ _ _ _ _) = id
> bindType (IInstanceDecl _ _ _ _ _ _ _) = id
> bindType (IHidingClassDecl _ _ _ _ _ _) = id

\end{verbatim}
The checks applied to the interface are similar to those performed
during syntax checking of type expressions.
\begin{verbatim}

> checkIDecl :: IDecl -> ISC IDecl
> checkIDecl (IInfixDecl  p fix pr op) = return (IInfixDecl p fix pr op)
> checkIDecl (HidingDataDecl p tc tvs) = do
>   checkTypeLhs tvs
>   return (HidingDataDecl p tc tvs)
> checkIDecl (IDataDecl p tc tvs cs) = do
>   checkTypeLhs tvs
>   liftM (IDataDecl p tc tvs) (mapM (liftMaybe (checkConstrDecl tvs)) cs)
> checkIDecl (INewtypeDecl p tc tvs nc) = do
>   checkTypeLhs tvs
>   liftM (INewtypeDecl p tc tvs) (checkNewConstrDecl tvs nc)
> checkIDecl (ITypeDecl p tc tvs ty) = do
>   checkTypeLhs tvs
>   liftM (ITypeDecl p tc tvs) (checkClosedType tvs ty)
> checkIDecl (IFunctionDecl p f n cx ty) =
>   liftM (IFunctionDecl p f n cx) (checkType ty)
> checkIDecl (IClassDecl p scls cls var tySigs defs deps) = 
>   liftM3 (IClassDecl p scls cls var) 
>          (mapM (\(b, sig) -> checkIDecl sig >>= \sig' -> return (b, sig')) tySigs)
>          (return defs) (return deps)
> checkIDecl i@(IInstanceDecl _ _ _ _ _ _ _) = return i 
> checkIDecl (IHidingClassDecl p scls cls var tySigs defs) = 
>  liftM2 (IHidingClassDecl p scls cls var) (mapM checkIDecl tySigs) (return defs)

> checkTypeLhs :: [Ident] -> ISC ()
> checkTypeLhs tvs = do
>   tyEnv <- getTypeEnv
>   let (tcs, tvs') = partition isTypeConstr tvs
>       isTypeConstr tv = not (null (lookupTopEnv tv tyEnv))
>   mapM_ (report . errNoVariable)       (nub tcs)
>   mapM_ (report . errNonLinear . head) (findMultiples tvs')

> checkConstrDecl :: [Ident] -> ConstrDecl -> ISC ConstrDecl
> checkConstrDecl tvs (ConstrDecl p evs c tys) = do
>   checkTypeLhs evs
>   liftM (ConstrDecl p evs c) (mapM (checkClosedType tvs') tys)
>   where tvs' = evs ++ tvs
> checkConstrDecl tvs (ConOpDecl p evs ty1 op ty2) = do
>   checkTypeLhs evs
>   liftM2 (\t1 t2 -> ConOpDecl p evs t1 op t2)
>          (checkClosedType tvs' ty1)
>          (checkClosedType tvs' ty2)
>   where tvs' = evs ++ tvs

> checkNewConstrDecl :: [Ident] -> NewConstrDecl -> ISC NewConstrDecl
> checkNewConstrDecl tvs (NewConstrDecl p evs c ty) = do
>   checkTypeLhs evs
>   liftM (NewConstrDecl p evs c) (checkClosedType tvs' ty)
>   where tvs' = evs ++ tvs

> checkClosedType :: [Ident] -> TypeExpr -> ISC TypeExpr
> checkClosedType tvs ty = do
>   ty' <- checkType ty
>   mapM_ (report . errUnboundVariable) (nub (filter (`notElem` tvs) (fv ty')))
>   return ty'

> checkType :: TypeExpr -> ISC TypeExpr
> checkType (ConstructorType tc tys) = checkTypeConstructor tc tys
> checkType (VariableType        tv) = checkType (ConstructorType (qualify tv) [])
> checkType (TupleType          tys) = liftM TupleType (mapM checkType tys)
> checkType (ListType            ty) = liftM ListType (checkType ty)
> checkType (ArrowType      ty1 ty2) = liftM2 ArrowType (checkType ty1) (checkType ty2)
> checkType (RecordType      fs mty) = liftM2 RecordType (mapM checkField fs)
>                                             (liftMaybe checkType mty)
>  where checkField (l, ty) = checkType ty >>= \ty' -> return (l, ty')
> checkType s@(SpecialConstructorType _ _) = 
>   checkType $ specialConsToTyExpr s

> checkTypeConstructor :: QualIdent -> [TypeExpr] -> ISC TypeExpr
> checkTypeConstructor tc tys = do
>   tyEnv <- getTypeEnv
>   case qualLookupTopEnv tc tyEnv of
>     [] | not (isQualified tc) && null tys -> return (VariableType (unqualify tc))
>        | otherwise                        -> do
>           report (errUndefinedType tc)
>           ConstructorType tc `liftM` mapM checkType tys
>     [Data _ _] -> ConstructorType tc `liftM` mapM checkType tys
>     [Alias  _] -> do
>                   report (errBadTypeSynonym tc)
>                   ConstructorType tc `liftM` mapM checkType tys
>     _          -> internalError "checkTypeConstructor"

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> liftMaybe :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
> liftMaybe f (Just x) = liftM Just (f x)
> liftMaybe _ Nothing  = return Nothing

\end{verbatim}
Error messages.
\begin{verbatim}

> errUndefinedType :: QualIdent -> Message
> errUndefinedType tc = posMessage tc
>                     $ text "Undefined type" <+> text (qualName tc)

> errNonLinear :: Ident -> Message
> errNonLinear tv = posMessage tv $ hsep $ map text
>   [ "Type variable", escName tv
>   , "occurs more than once on left hand side of type declaration"
>   ]

> errNoVariable :: Ident -> Message
> errNoVariable tv = posMessage tv $ hsep $ map text
>   [ "Type constructor", escName tv
>   , "used in left hand side of type declaration"
>   ]

> errUnboundVariable :: Ident -> Message
> errUnboundVariable tv = posMessage tv $
>   text "Undefined type variable" <+> text (escName tv)

> errBadTypeSynonym :: QualIdent -> Message
> errBadTypeSynonym tc = posMessage tc $ text "Synonym type"
>                     <+> text (qualName tc) <+> text "in interface"

\end{verbatim}
