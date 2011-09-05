{- |
    Module      :  $Header$
    Description :  Handling of record syntax
    Copyright   :  (c) 2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Fully expand all (imported) record types within the type constructor
    environment and the type environment.
    /Note:/ the record types for the current module are expanded within the
    type check.
-}
module Records where

import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import Curry.Base.Ident
import Curry.Syntax

import Base.CurryTypes (toType)
import Base.Messages
import Base.TopEnv
import Base.Types
import Base.TypeSubst

import Env.Interface
import Env.Label
import Env.TypeConstructors
import Env.Value

import CompilerEnv
import CompilerOpts

-- ---------------------------------------------------------------------------
-- Import defined record labels
-- ---------------------------------------------------------------------------

-- Unlike usual identifiers like in functions, types etc., identifiers
-- of labels are always represented unqualified within the whole context
-- of compilation. Since the common type environment (type \texttt{ValueEnv})
-- has some problems with handling imported unqualified identifiers, it is
-- necessary to add the type information for labels seperately. For this reason
-- the function \texttt{importLabels} generates an environment containing
-- all imported labels and the function \texttt{addImportedLabels} adds this
-- content to a value environment.

importLabels :: InterfaceEnv -> [ImportDecl] -> LabelEnv
importLabels mEnv ds = foldl importLabelTypes initLabelEnv ds
  where
    importLabelTypes :: LabelEnv -> ImportDecl -> LabelEnv
    importLabelTypes lEnv (ImportDecl p m _ asM is) =
      case Map.lookup m mEnv of
        Just (Interface _ _ ds') -> foldl (importLabelType p (fromMaybe m asM) is) lEnv ds'
        Nothing  -> internalError "Records.importLabels"

    importLabelType p m is lEnv (ITypeDecl _ r _ (RecordType fs _)) =
     foldl (insertLabelType p m r' (getImportSpec r' is)) lEnv fs
     where r' = qualifyWith m (fromRecordExtId (unqualify r))
    importLabelType _ _ _  lEnv _ = lEnv

    insertLabelType _ _ r (Just (ImportTypeAll _)) lEnv ([l],ty) =
      bindLabelType l r (toType [] ty) lEnv
    insertLabelType _ _ r (Just (ImportTypeWith _ ls)) lEnv ([l],ty)
      | l `elem` ls = bindLabelType l r (toType [] ty) lEnv
      | otherwise   = lEnv
    insertLabelType _ _ _ _ lEnv _ = lEnv

    getImportSpec r (Just (Importing _ is')) =
      find (isImported (unqualify r)) is'
    getImportSpec r Nothing = Just (ImportTypeAll (unqualify r))
    getImportSpec _ _ = Nothing

    isImported r (Import         r'  ) = r == r'
    isImported r (ImportTypeWith r' _) = r == r'
    isImported r (ImportTypeAll  r'  ) = r == r'

addImportedLabels :: ModuleIdent -> LabelEnv -> ValueEnv -> ValueEnv
addImportedLabels m lEnv tyEnv =
  foldr addLabelType tyEnv $ concat $ Map.elems lEnv
  where
  addLabelType (LabelType l r ty) tyEnv' =
    let m' = fromMaybe m (qualidMod r)
    in  importTopEnv m' l
                     (Label (qualify l) (qualQualify m' r) (polyType ty))
               tyEnv'




recordExpansion1 :: Options -> CompilerEnv -> CompilerEnv
recordExpansion1 opts env
  | enabled   = env { tyConsEnv = tcEnv', valueEnv = tyEnv' }
  | otherwise = env
  where
    enabled  = Records `elem` optExtensions opts
    tcEnv'   = fmap (expandRecordTC    tcEnv) tcEnv
    tyEnv'   = fmap (expandRecordTypes tcEnv) tyEnvLbl
    tyEnvLbl = addImportedLabels m lEnv tyEnv
    m        = moduleIdent env
    lEnv     = labelEnv env
    tcEnv    = tyConsEnv env
    tyEnv    = valueEnv env

recordExpansion2 :: Options -> CompilerEnv -> CompilerEnv
recordExpansion2 opts env
  | enabled  = env { valueEnv = tyEnv' }
  | otherwise = env
  where
    enabled  = Records `elem` optExtensions opts
    tyEnv'   = fmap (expandRecordTypes tcEnv) tyEnvLbl
    tyEnvLbl = addImportedLabels m lEnv tyEnv
    m        = moduleIdent env
    lEnv     = labelEnv env
    tcEnv    = tyConsEnv env
    tyEnv    = valueEnv env





expandRecordTC :: TCEnv -> TypeInfo -> TypeInfo
expandRecordTC tcEnv (DataType qid n args) =
  DataType qid n (map (maybe Nothing (Just . (expandData tcEnv))) args)
expandRecordTC tcEnv (RenamingType qid n (DataConstr ident m [ty])) =
  RenamingType qid n (DataConstr ident m [expandRecords tcEnv ty])
expandRecordTC _     (RenamingType _   _ (DataConstr _     _  _)) =
  internalError "Records.expandRecordTC"
expandRecordTC tcEnv (AliasType qid n ty) =
  AliasType qid n (expandRecords tcEnv ty)

expandData :: TCEnv -> DataConstr -> DataConstr
expandData tcEnv (DataConstr ident n tys) =
  DataConstr ident n (map (expandRecords tcEnv) tys)

expandRecordTypes :: TCEnv -> ValueInfo -> ValueInfo
expandRecordTypes tcEnv (DataConstructor qid (ForAllExist n m ty)) =
  DataConstructor qid (ForAllExist n m (expandRecords tcEnv ty))
expandRecordTypes tcEnv (NewtypeConstructor qid (ForAllExist n m ty)) =
  NewtypeConstructor qid (ForAllExist n m (expandRecords tcEnv ty))
expandRecordTypes tcEnv (Value qid (ForAll n ty)) =
  Value qid (ForAll n (expandRecords tcEnv ty))
expandRecordTypes tcEnv (Label qid r (ForAll n ty)) =
  Label qid r (ForAll n (expandRecords tcEnv ty))

expandRecords :: TCEnv -> Type -> Type
expandRecords tcEnv (TypeConstructor qid tys) =
  case (qualLookupTC qid tcEnv) of
    [AliasType _ _ rty@(TypeRecord _ _)]
      -> expandRecords tcEnv
           (expandAliasType (map (expandRecords tcEnv) tys) rty)
    _ -> TypeConstructor qid (map (expandRecords tcEnv) tys)
expandRecords tcEnv (TypeConstrained tys v) =
  TypeConstrained (map (expandRecords tcEnv) tys) v
expandRecords tcEnv (TypeArrow ty1 ty2) =
  TypeArrow (expandRecords tcEnv ty1) (expandRecords tcEnv ty2)
expandRecords tcEnv (TypeRecord fs rv) =
  TypeRecord (map (\ (l,ty) -> (l,expandRecords tcEnv ty)) fs) rv
expandRecords _ ty = ty
