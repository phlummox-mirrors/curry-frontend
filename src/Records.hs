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
module Records (expandTCValueEnv, expandValueEnv) where

import Base.Messages (internalError)
import Base.Types
import Base.TypeSubst (expandAliasType)

import Env.TypeConstructors
import Env.Value

import CompilerEnv
import CompilerOpts

expandTCValueEnv :: Options -> CompilerEnv -> CompilerEnv
expandTCValueEnv opts env
  | enabled   = env' { tyConsEnv = tcEnv' }
  | otherwise = env
  where
  enabled = Records `elem` optExtensions opts
  tcEnv'  = fmap (expandRecordTC tcEnv) tcEnv
  tcEnv   = tyConsEnv env'
  env'    = expandValueEnv opts env

expandRecordTC :: TCEnv -> TypeInfo -> TypeInfo
expandRecordTC tcEnv (DataType qid n args) =
  DataType qid n $ map (fmap expandData) args
  where
  expandData (DataConstr c m tys) =
    DataConstr c m $ map (expandRecords tcEnv) tys
expandRecordTC tcEnv (RenamingType qid n (DataConstr c m [ty])) =
  RenamingType qid n (DataConstr c m [expandRecords tcEnv ty])
expandRecordTC _     (RenamingType _   _ (DataConstr    _ _ _)) =
  internalError "Records.expandRecordTC"
expandRecordTC tcEnv (AliasType qid n ty) =
  AliasType qid n (expandRecords tcEnv ty)

expandValueEnv :: Options -> CompilerEnv -> CompilerEnv
expandValueEnv opts env
  | enabled   = env { valueEnv = tyEnv' }
  | otherwise = env
  where
  tcEnv    = tyConsEnv env
  tyEnv    = valueEnv env
  enabled  = Records `elem` optExtensions opts
  tyEnv'   = fmap (expandRecordTypes tcEnv) tyEnv -- $ addImportedLabels m lEnv tyEnv
--   m        = moduleIdent env
--   lEnv     = labelEnv env

expandRecordTypes :: TCEnv -> ValueInfo -> ValueInfo
expandRecordTypes tcEnv (DataConstructor  qid a (ForAllExist n m ty)) =
  DataConstructor qid a (ForAllExist n m (expandRecords tcEnv ty))
expandRecordTypes tcEnv (NewtypeConstructor qid (ForAllExist n m ty)) =
  NewtypeConstructor qid (ForAllExist n m (expandRecords tcEnv ty))
expandRecordTypes tcEnv (Value qid a (ForAll n ty)) =
  Value qid a (ForAll n (expandRecords tcEnv ty))
expandRecordTypes tcEnv (Label qid r (ForAll n ty)) =
  Label qid r (ForAll n (expandRecords tcEnv ty))

expandRecords :: TCEnv -> Type -> Type
expandRecords tcEnv (TypeConstructor qid tys) = case qualLookupTC qid tcEnv of
  [AliasType _ _ rty@(TypeRecord _ _)]
    -> expandRecords tcEnv $ expandAliasType (map (expandRecords tcEnv) tys) rty
  _ -> TypeConstructor qid $ map (expandRecords tcEnv) tys
expandRecords tcEnv (TypeConstrained tys v) =
  TypeConstrained (map (expandRecords tcEnv) tys) v
expandRecords tcEnv (TypeArrow ty1 ty2) =
  TypeArrow (expandRecords tcEnv ty1) (expandRecords tcEnv ty2)
expandRecords tcEnv (TypeRecord fs rv) =
  TypeRecord (map (\ (l, ty) -> (l, expandRecords tcEnv ty)) fs) rv
expandRecords _ ty = ty

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

-- importLabels :: InterfaceEnv -> [ImportDecl] -> LabelEnv
-- importLabels mEnv ds = foldl importLabelTypes initLabelEnv ds
--   where
--   importLabelTypes :: LabelEnv -> ImportDecl -> LabelEnv
--   importLabelTypes lEnv (ImportDecl _ m _ asM is) = case Map.lookup m mEnv of
--     Just (Interface _ _ ds') ->
--       foldl (importLabelType (fromMaybe m asM) is) lEnv ds'
--     Nothing  ->
--       internalError "Records.importLabels"
--
--   importLabelType m is lEnv (ITypeDecl _ r _ (RecordType fs _)) =
--     foldl (insertLabelType r' (getImportSpec r' is)) lEnv fs
--     where r' = qualifyWith m $ fromRecordExtId $ unqualify r
--   importLabelType _ _  lEnv _ = lEnv
--
--   insertLabelType r (Just (ImportTypeAll     _)) lEnv ([l], ty) =
--     bindLabelType l r (toType [] ty) lEnv
--   insertLabelType r (Just (ImportTypeWith _ ls)) lEnv ([l], ty)
--     | l `elem` ls = bindLabelType l r (toType [] ty) lEnv
--     | otherwise   = lEnv
--   insertLabelType _ _ lEnv _ = lEnv
--
--   getImportSpec r (Just (Importing _ is')) = find (isImported (unqualify r)) is'
--   getImportSpec r Nothing                  = Just $ ImportTypeAll $ unqualify r
--   getImportSpec _ _                        = Nothing
--
--   isImported r (Import         r'  ) = r == r'
--   isImported r (ImportTypeWith r' _) = r == r'
--   isImported r (ImportTypeAll  r'  ) = r == r'

-- addImportedLabels :: ModuleIdent -> LabelEnv -> ValueEnv -> ValueEnv
-- addImportedLabels m lEnv tyEnv =
--   foldr addLabelType tyEnv (concat $ Map.elems lEnv)
--   where
--   addLabelType (LabelType l r ty) = importTopEnv m' l lblInfo
--     where lblInfo = Label (qualify l) (qualQualify m' r) (polyType ty)
--           m' = fromMaybe m (qualidMod r)
