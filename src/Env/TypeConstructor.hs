{- |
    Module      :  $Header$
    Description :  Environment of type constructors
    Copyright   :  (c) 2002 - 2004 Wolfgang Lux
                       2011        Björn Peemöller
                       2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    For all defined types the compiler must maintain kind information.
    For algebraic data types and renaming types the compiler also records
    all data constructors belonging to that type, for alias types the
    type expression to be expanded is saved. Futhermore, recording the
    arity is necessary for alias types because the right hand side, i.e.,
    the type expression, can have arbitrary kind and therefore the type
    alias' arity cannot be determined from its own kind. For instance,
    the type alias type List = [] has the kind * -> *, but its arity is 0.
    In order to manage the import and export of types, the names of the
    original definitions are also recorded. On import two types are
    considered equal if their original names match.

    The information for a data constructor comprises the number of
    existentially quantified type variables and the list of the argument
    types. Note that renaming type constructors have only one type
    argument.

    For type classes the names of their immediate super classes and
    their methods are saved. Type classes are recorded in the type
    constructor environment because type constructors and type classes
    share a common name space.

    For type variables only their kind is recorded in the environment.

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
-}

module Env.TypeConstructor
  ( TypeInfo (..), tcKind, classKind, varKind
  , TCEnv, initTCEnv, bindTypeInfo
  , lookupTypeInfo, qualLookupTypeInfo, qualLookupTypeInfoUnique
  ) where

import Curry.Base.Ident

import Base.Kinds
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.Utils ((++!))

data TypeInfo
  = DataType     QualIdent Kind [DataConstr]
  | RenamingType QualIdent Kind DataConstr
  | AliasType    QualIdent Kind Int Type
  | TypeClass    QualIdent Kind [QualIdent] [Ident]
  | TypeVar      Kind
    deriving Show

instance Entity TypeInfo where
  origName (DataType     tc    _ _) = tc
  origName (RenamingType tc    _ _) = tc
  origName (AliasType    tc  _ _ _) = tc
  origName (TypeClass    cls _ _ _) = cls
  origName (TypeVar              _) =
    internalError "Env.TypeConstructor.origName: type variable"

  -- TODO: merge only if kind is equal?
  merge (DataType tc k cs) (DataType tc' _ cs')
    | tc == tc' && (null cs || null cs' || cs == cs') =
    Just $ DataType tc k $ if null cs then cs' else cs
  merge (DataType tc k _) (RenamingType tc' _ nc)
    | tc == tc' = Just (RenamingType tc k nc)
  merge l@(RenamingType tc _ _) (DataType tc' _ _)
    | tc == tc' = Just l
  merge l@(RenamingType tc _ _) (RenamingType tc' _ _)
    | tc == tc' = Just l
  merge l@(AliasType tc _ _ _) (AliasType tc' _ _ _)
    | tc == tc' = Just l
  -- TODO: merge only if super classes are equal?
  merge (TypeClass cls k sclss ms) (TypeClass cls' _ _ ms')
    | cls == cls' && (null ms || null ms' || ms == ms') =
    Just $ TypeClass cls k sclss $ if null ms then ms' else ms
  merge _ _ = Nothing

tcKind :: QualIdent -> TCEnv -> Kind
tcKind qtc tcEnv = case qualLookupTypeInfo qtc tcEnv of
  [DataType     _ k   _] -> k
  [RenamingType _ k   _] -> k
  [AliasType    _ k _ _] -> k
  _                      ->
    internalError "Env.TypeConstructor.tcKind: no type constructor"

classKind :: QualIdent -> TCEnv -> Kind
classKind qcls tcEnv = case qualLookupTypeInfo qcls tcEnv of
  [TypeClass _ k _ _] -> k
  _                   ->
    internalError "Env.TypeConstructor.classKind: no type class"

varKind :: Ident -> TCEnv -> Kind
varKind tv tcEnv = case lookupTypeInfo tv tcEnv of
  [TypeVar k] -> k
  _           -> internalError "Env.TypeConstructor.varKind: no type variable"

-- Types can only be defined on the top-level; no nested environments are
-- needed for them. Tuple types must be handled as a special case because
-- there is an infinite number of potential tuple types making it
-- impossible to insert them into the environment in advance.

type TCEnv = TopEnv TypeInfo

initTCEnv :: TCEnv
initTCEnv = emptyTopEnv

bindTypeInfo :: ModuleIdent -> Ident -> TypeInfo -> TCEnv -> TCEnv
bindTypeInfo m ident ti = bindTopEnv ident ti . qualBindTopEnv qident ti
  where
    qident = qualifyWith m ident

lookupTypeInfo :: Ident -> TCEnv -> [TypeInfo]
lookupTypeInfo ident tcEnv = lookupTopEnv ident tcEnv ++! lookupTupleTC ident

qualLookupTypeInfo :: QualIdent -> TCEnv -> [TypeInfo]
qualLookupTypeInfo ident tcEnv =
  qualLookupTopEnv ident tcEnv ++! lookupTupleTC (unqualify ident)

qualLookupTypeInfoUnique :: ModuleIdent -> QualIdent -> TCEnv -> [TypeInfo]
qualLookupTypeInfoUnique m qident tcEnv =
  case qualLookupTypeInfo qident tcEnv of
    []   -> []
    [ti] -> [ti]
    tis  -> case qualLookupTypeInfo (qualQualify m qident) tcEnv of
      []  -> tis
      [ti] -> [ti]
      tis' -> tis'

lookupTupleTC :: Ident -> [TypeInfo]
lookupTupleTC tc | isTupleId tc = [tupleTCs !! (tupleArity tc - 2)]
                 | otherwise    = []

tupleTCs :: [TypeInfo]
tupleTCs = map typeInfo tupleData
  where
    typeInfo dc@(DataConstr _ n _)  = DataType (qTupleId n) (simpleKind n) [dc]
    typeInfo (RecordConstr _ _ _ _) =
      internalError "Env.TypeConstructor.tupleTCs: record constructor"
