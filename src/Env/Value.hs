{- |
    Module      :  $Header$
    Description :  Environment for functions, constructors and labels
    Copyright   :  (c) 2001-2004, Wolfgang Lux
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    In order to test the type correctness of a module, the compiler needs
    to determine the type of every data constructor, function,
    variable, record and label in the module.
    For the purpose of type checking there is no
    need for distinguishing between variables and functions. For all objects
    their original names and their types are saved. Functions also
    contain arity information. Labels currently contain the name of their
    defining record. On import two values
    are considered equal if their original names match.
-}

module Env.Value
  ( ValueEnv, ValueInfo (..)
  , bindGlobalInfo, bindFun, qualBindFun, rebindFun, unbindFun, bindLabel
  , lookupValue, qualLookupValue, qualLookupCons, lookupTuple, tupleDCs
  , initDCEnv, ppTypes ) where

import Text.PrettyPrint (Doc, vcat)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.CurryTypes (fromQualType)
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.Utils ((++!))

import Env.TypeConstructor (TypeInfo (..), tupleTCs)

data ValueInfo
  -- |Data constructor with original name, arity and type
  = DataConstructor    QualIdent Int       ExistTypeScheme
  -- |Newtype constructor with original name and type (arity is always 1)
  | NewtypeConstructor QualIdent           ExistTypeScheme
  -- |Value with original name, arity and type
  | Value              QualIdent Int       TypeScheme
  -- |Record label with original name, record name and type
  | Label              QualIdent QualIdent TypeScheme
    deriving Show

instance Entity ValueInfo where
  origName (DataConstructor    orgName _ _) = orgName
  origName (NewtypeConstructor orgName   _) = orgName
  origName (Value              orgName _ _) = orgName
  origName (Label              orgName _ _) = orgName

  merge (Label l r ty) (Label l' r' _)
    | l == l' && r == r' = Just $ Label l r ty
    | otherwise          = Nothing
  merge x y
    | origName x == origName y = Just x
    | otherwise                = Nothing

-- Even though value declarations may be nested, the compiler uses only
-- flat environments for saving type information. This is possible
-- because all identifiers are renamed by the compiler. Here we need
-- special cases for handling tuple constructors.
--
-- \em{Note:} the function \texttt{qualLookupValue} has been extended to
-- allow the usage of the qualified list constructor \texttt{(Prelude.:)}.

type ValueEnv = TopEnv ValueInfo

bindGlobalInfo :: (QualIdent -> a -> ValueInfo) -> ModuleIdent -> Ident -> a
               -> ValueEnv -> ValueEnv
bindGlobalInfo f m c ty = bindTopEnv fun c v . qualBindTopEnv fun qc v
  where qc  = qualifyWith m c
        v   = f qc ty
        fun = "Env.Value.bindGlobalInfo"

bindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
bindFun m f a ty
  | idUnique f == 0 = bindTopEnv fun f v . qualBindTopEnv fun qf v
  | otherwise       = bindTopEnv fun f v
  where qf  = qualifyWith m f
        v   = Value qf a ty
        fun = "Env.Value.bindFun"

qualBindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
qualBindFun m f a ty = qualBindTopEnv "Env.Value.qualBindFun" qf $
  Value qf a ty
  where qf = qualifyWith m f

rebindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv
          -> ValueEnv
rebindFun m f a ty
  | idUnique f == 0 = rebindTopEnv f v . qualRebindTopEnv qf v
  | otherwise       = rebindTopEnv f v
  where qf = qualifyWith m f
        v = Value qf a ty

unbindFun :: Ident -> ValueEnv -> ValueEnv
unbindFun = unbindTopEnv

bindLabel :: Ident -> QualIdent -> TypeScheme -> ValueEnv -> ValueEnv
bindLabel l r ty tyEnv = bindTopEnv "Env.Value.bindLabel" l v tyEnv
  where v  = Label (qualify l) r ty

lookupValue :: Ident -> ValueEnv -> [ValueInfo]
lookupValue x tyEnv = lookupTopEnv x tyEnv ++! lookupTuple x

qualLookupValue :: QualIdent -> ValueEnv -> [ValueInfo]
qualLookupValue x tyEnv = qualLookupTopEnv x tyEnv
                          ++! qualLookupCons x tyEnv
                          ++! lookupTuple (unqualify x)

qualLookupCons :: QualIdent -> ValueEnv -> [ValueInfo]
qualLookupCons x tyEnv
  | mmid == Just preludeMIdent && qid == consId
  = qualLookupTopEnv (qualify qid) tyEnv
  | otherwise = []
 where (mmid, qid) = (qidModule x, qidIdent x)

lookupTuple :: Ident -> [ValueInfo]
lookupTuple c
  | isTupleId c = [tupleDCs !! (tupleArity c - 2)]
  | otherwise = []

tupleDCs :: [ValueInfo]
tupleDCs = map dataInfo tupleTCs
  where
  dataInfo (DataType tc _ [Just (DataConstr _ _ tys)]) =
    DataConstructor (qualUnqualify preludeMIdent tc) (length tys)
      (ForAllExist (length tys) 0 $ foldr TypeArrow (tupleType tys) tys)
  dataInfo _ = internalError "Env.Value.tupleDCs: no data constructor"

initDCEnv :: ValueEnv
initDCEnv = foldr predefDC emptyTopEnv
  [ (c, length tys, constrType (polyType ty) n' tys)
  | (ty, cs) <- predefTypes, DataConstr c n' tys <- cs]
  where predefDC (c, a, ty) = predefTopEnv c' (DataConstructor c' a ty)
          where c' = qualify c
        constrType (ForAll n ty) n' = ForAllExist n n' . foldr TypeArrow ty

-- |Pretty-printing the types from the type environment
ppTypes :: ModuleIdent -> ValueEnv -> Doc
ppTypes mid valueEnv = ppTypes' mid $ localBindings valueEnv
  where
  ppTypes' :: ModuleIdent -> [(Ident, ValueInfo)] -> Doc
  ppTypes' m = vcat . map (ppIDecl . mkDecl) . filter (isValue . snd)
    where
    mkDecl (v, Value _ a (ForAll _ ty)) =
      IFunctionDecl NoPos (qualify v) a (fromQualType m ty)
    mkDecl _ = internalError "Env.Value.ppTypes: no value"
    isValue (Value _ _ _) = True
    isValue _             = False
