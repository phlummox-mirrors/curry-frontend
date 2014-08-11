{- |
    Module      :  $Header$
    Description :  Importing interface declarations
    Copyright   :  (c) 2000 - 2003, Wolfgang Lux
                       2011       , Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importModules' to bring the imported
    entities into the module's scope, and the function 'qualifyEnv' to
    qualify the environment prior to computing the export interface.
-}
module Imports (importInterfaces, importModules, qualifyEnv) where

import           Control.Monad                   (liftM, unless)
import qualified Control.Monad.State        as S (State, gets, modify, runState)
import           Control.Monad.Trans.Either
import qualified Data.Map                   as Map
import           Data.Maybe
import qualified Data.Set                   as Set

import Curry.Base.Ident
import Curry.Base.Monad
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.CurryTypes (toQualType, toQualTypes)
import Base.Messages
import Base.TopEnv
import Base.Types
import Base.TypeSubst (expandAliasType)

import Env.Interface
import Env.ModuleAlias (importAliases, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

import CompilerEnv
import CompilerOpts

-- |The function 'importModules' brings the declarations of all
-- imported interfaces into scope for the current module.
importModules :: Monad m => Options -> Module -> InterfaceEnv -> CYT m CompilerEnv
importModules opts mdl@(Module _ mid _ imps _) iEnv
  = case foldl importModule (initEnv, []) imps of
      (e, []  ) -> right $ expandTCValueEnv opts $ importUnifyData e
      (_, errs) -> left errs
  where
    initEnv = (initCompilerEnv mid)
      { aliasEnv     = importAliases imps -- import module aliases
      , interfaceEnv = iEnv               -- imported interfaces
      , extensions   = knownExtensions mdl
      }
    importModule (env, msgs) (ImportDecl _ m q asM is) =
      case Map.lookup m iEnv of
        Just intf -> let (env', msgs') = importInterface (fromMaybe m asM) q is intf env
                     in  (env', msgs ++ msgs')
        Nothing   -> internalError $ "Imports.importModules: no interface for "
                                    ++ show m

-- |The function 'importInterfaces' brings the declarations of all
-- imported interfaces into scope for the current 'Interface'.
importInterfaces :: Options -> Interface -> InterfaceEnv -> CompilerEnv
importInterfaces opts (Interface m is _) iEnv
  = (expandTCValueEnv opts . importUnifyData)
  $ foldl importModule initEnv is
  where
    initEnv = (initCompilerEnv m) { aliasEnv = initAliasEnv, interfaceEnv = iEnv }
    importModule env (IImportDecl _ i) = case Map.lookup i iEnv of
        Just intf -> importInterfaceIntf intf env
        Nothing   -> internalError $ "Imports.importInterfaces: no interface for "
                                    ++ show m

-- ---------------------------------------------------------------------------
-- Importing an interface into the module
-- ---------------------------------------------------------------------------

-- Three kinds of environments are computed from the interface:
--
-- 1. The operator precedences
-- 2. The type constructors
-- 3. The types of the data constructors and functions (values)
--
-- Note that the original names of all entities defined in the imported module
-- are qualified appropriately. The same is true for type expressions.

type IdentMap    = Map.Map Ident

type ExpPEnv     = IdentMap PrecInfo
type ExpTCEnv    = IdentMap TypeInfo
type ExpValueEnv = IdentMap ValueInfo

-- When an interface is imported, the compiler first transforms the
-- interface into these environments. If an import specification is
-- present, the environments are restricted to only those entities which
-- are included in the specification or not hidden by it, respectively.
-- The resulting environments are then imported into the current module
-- using either a qualified import (if the module is imported qualified)
-- or both a qualified and an unqualified import (non-qualified import).

importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec -> Interface
                -> CompilerEnv -> (CompilerEnv, [Message])
importInterface m q is i env = (env', errs)
  where
  env' = env
    { opPrecEnv = importEntities m q vs id              mPEnv  $ opPrecEnv env
    , tyConsEnv = importEntities m q ts (importData vs) mTCEnv $ tyConsEnv env
    , valueEnv  = importEntities m q vs id              mTyEnv $ valueEnv  env
    }
  mPEnv  = intfEnv bindPrec i -- all operator precedences
  mTCEnv = intfEnv bindTC   i -- all type constructors
  mTyEnv = intfEnv bindTy   i -- all values
  -- all imported type constructors / values
  (expandedSpec, errs) = runExpand (expandSpecs is) m mTCEnv mTyEnv
  ts = isVisible is (Set.fromList $ foldr addType  [] expandedSpec)
  vs = isVisible is (Set.fromList $ foldr addValue [] expandedSpec)

addType :: Import -> [Ident] -> [Ident]
addType (Import            _) tcs = tcs
addType (ImportTypeWith tc _) tcs = tc : tcs
addType (ImportTypeAll     _) _   = internalError "Imports.addType"

addValue :: Import -> [Ident] -> [Ident]
addValue (Import            f) fs = f : fs
addValue (ImportTypeWith _ cs) fs = cs ++ fs
addValue (ImportTypeAll     _) _  = internalError "Imports.addValue"

isVisible :: Maybe ImportSpec -> Set.Set Ident -> Ident -> Bool
isVisible Nothing                _  = const True
isVisible (Just (Importing _ _)) xs = (`Set.member`    xs)
isVisible (Just (Hiding    _ _)) xs = (`Set.notMember` xs)

importEntities :: Entity a => ModuleIdent -> Bool -> (Ident -> Bool)
               -> (a -> a) -> IdentMap a -> TopEnv a -> TopEnv a
importEntities m q isVisible' f mEnv env =
  foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
        [(x,f y) | (x,y) <- Map.toList mEnv, isVisible' x]
  where importUnqual m' x y = importTopEnv m' x y . qualImportTopEnv m' x y

importData :: (Ident -> Bool) -> TypeInfo -> TypeInfo
importData isVisible' (DataType tc n cs) =
  DataType tc n (map (>>= importConstr isVisible') cs)
importData isVisible' (RenamingType tc n nc) =
  maybe (DataType tc n []) (RenamingType tc n) (importConstr isVisible' nc)
importData _ (AliasType tc n ty) = AliasType tc n ty

importConstr :: (Ident -> Bool) -> DataConstr -> Maybe DataConstr
importConstr isVisible' dc@(DataConstr c _ _)
  | isVisible' c = Just dc
  | otherwise    = Nothing

-- ---------------------------------------------------------------------------
-- Building the initial environment
-- ---------------------------------------------------------------------------

-- In a first step, the four export environments are initialized from
-- the interface's declarations. This step also qualifies the names of
-- all entities defined in (but not imported into) the interface with its
-- module name.

intfEnv :: (ModuleIdent -> IDecl -> IdentMap a -> IdentMap a)
        -> Interface -> IdentMap a
intfEnv bind (Interface m _ ds) = foldr (bind m) Map.empty ds

-- operator precedences
bindPrec :: ModuleIdent -> IDecl -> ExpPEnv -> ExpPEnv
bindPrec m (IInfixDecl _ fix prec op) =
  Map.insert (unqualify op) (PrecInfo (qualQualify m op) (OpPrec fix prec))
bindPrec _ _ = id

bindTCHidden :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
bindTCHidden m (HidingDataDecl _ tc tvs) = bindType DataType m tc tvs []
bindTCHidden m d                         = bindTC m d

-- type constructors
bindTC :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
bindTC m (IDataDecl _ tc tvs cs) mTCEnv
  | unqualify tc `Map.member` mTCEnv = mTCEnv
  | otherwise = bindType DataType m tc tvs (map (fmap mkData) cs) mTCEnv
  where
   mkData (ConstrDecl _ evs c tys) =
     DataConstr c (length evs) (toQualTypes m tvs tys)
   mkData (ConOpDecl _ evs ty1 c ty2) =
     DataConstr c (length evs) (toQualTypes m tvs [ty1,ty2])

bindTC m (INewtypeDecl _ tc tvs (NewConstrDecl _ evs c ty)) mTCEnv =
  bindType RenamingType m tc tvs
 (DataConstr c (length evs) [toQualType m tvs ty]) mTCEnv

bindTC m (ITypeDecl _ tc tvs ty) mTCEnv
  | isRecordExtId tc' =
    bindType AliasType m (qualify (fromRecordExtId tc')) tvs
   (toQualType m tvs ty) mTCEnv
  | otherwise =
    bindType AliasType m tc tvs (toQualType m tvs ty) mTCEnv
  where tc' = unqualify tc

bindTC _ _ mTCEnv = mTCEnv

bindType :: (QualIdent -> Int -> a -> TypeInfo) -> ModuleIdent -> QualIdent
         -> [Ident] -> a -> ExpTCEnv -> ExpTCEnv
bindType f m tc tvs = Map.insert (unqualify tc)
                    . f (qualQualify m tc) (length tvs)

-- functions and data constructors
bindTy :: ModuleIdent -> IDecl -> ExpValueEnv -> ExpValueEnv
bindTy m (IDataDecl _ tc tvs cs) env =
  foldr (bindConstr m tc' tvs $ constrType tc' tvs) env $ catMaybes cs
  where tc' = qualQualify m tc
bindTy m (INewtypeDecl _ tc tvs nc) env =
  bindNewConstr m tc' tvs (constrType tc' tvs) nc env
  where tc' = qualQualify m tc
bindTy m (ITypeDecl _ rtc tvs (RecordType fs _)) env =
  foldr (bindRecordLabels m rtc') env' fs
  where urtc = fromRecordExtId $ unqualify rtc
        rtc' = qualifyWith m urtc
        env' = bindConstr m rtc' tvs (constrType rtc' tvs)
               (ConstrDecl NoPos [] urtc (map snd fs)) env
bindTy m (IFunctionDecl _ f a ty) env = Map.insert (unqualify f)
  (Value (qualQualify m f) a (polyType (toQualType m [] ty))) env
bindTy _ _ env = env

bindConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl
           -> ExpValueEnv -> ExpValueEnv
bindConstr m tc tvs ty0 (ConstrDecl     _ evs c tys) = Map.insert c $
  DataConstructor (qualifyLike tc c) (length tys) $
  constrType' m tvs evs (foldr ArrowType ty0 tys)
bindConstr m tc tvs ty0 (ConOpDecl _ evs ty1 op ty2) = Map.insert op $
  DataConstructor (qualifyLike tc op) 2 $
  constrType' m tvs evs (ArrowType ty1 (ArrowType ty2 ty0))

bindNewConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr
              -> NewConstrDecl -> ExpValueEnv -> ExpValueEnv
bindNewConstr m tc tvs ty0 (NewConstrDecl _ evs c ty1) = Map.insert c $
  NewtypeConstructor (qualifyLike tc c) $
  constrType' m tvs evs (ArrowType ty1 ty0)

constrType' :: ModuleIdent -> [Ident] -> [Ident] -> TypeExpr -> ExistTypeScheme
constrType' m tvs evs ty = ForAllExist (length tvs) (length evs)
                                       (toQualType m tvs ty)

bindRecordLabels :: ModuleIdent -> QualIdent -> ([Ident], TypeExpr)
                 -> ExpValueEnv -> ExpValueEnv
bindRecordLabels m r (ls, ty) env = foldr bindLbl env ls
  where
  bindLbl l = Map.insert l (lblInfo l)
  lblInfo l = Label (qualify l) r (polyType $ toQualType m [] ty)

constrType :: QualIdent -> [Ident] -> TypeExpr
constrType tc tvs = ConstructorType tc $ map VariableType tvs

-- ---------------------------------------------------------------------------
-- Expansion of the import specification
-- ---------------------------------------------------------------------------

-- After the environments have been initialized, the optional import
-- specifications can be checked. There are two kinds of import
-- specifications, a ``normal'' one, which names the entities that shall
-- be imported, and a hiding specification, which lists those entities
-- that shall not be imported.
--
-- There is a subtle difference between both kinds of
-- specifications: While it is not allowed to list a data constructor
-- outside of its type in a ``normal'' specification, it is allowed to
-- hide a data constructor explicitly. E.g., if module \texttt{A} exports
-- the data type \texttt{T} with constructor \texttt{C}, the data
-- constructor can be imported with one of the two specifications
--
-- import A (T(C))
-- import A (T(..))
--
-- but can be hidden in three different ways:
--
-- import A hiding (C)
-- import A hiding (T (C))
-- import A hiding (T (..))
--
-- The functions \texttt{expandImport} and \texttt{expandHiding} check
-- that all entities in an import specification are actually exported
-- from the module. In addition, all imports of type constructors are
-- changed into a \texttt{T()} specification and explicit imports for the
-- data constructors are added.

data ExpandState = ExpandState
  { expModIdent :: ModuleIdent
  , expTCEnv    :: ExpTCEnv
  , expValueEnv :: ExpValueEnv
  , errors      :: [Message]
  }

type ExpandM a = S.State ExpandState a

getModuleIdent :: ExpandM ModuleIdent
getModuleIdent = S.gets expModIdent

getTyConsEnv :: ExpandM ExpTCEnv
getTyConsEnv = S.gets expTCEnv

getValueEnv :: ExpandM ExpValueEnv
getValueEnv = S.gets expValueEnv

report :: Message -> ExpandM ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

runExpand :: ExpandM a -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> (a, [Message])
runExpand expand m tcEnv tyEnv =
  let (r, s) = S.runState expand (ExpandState m tcEnv tyEnv [])
  in (r, reverse $ errors s)

expandSpecs :: Maybe ImportSpec -> ExpandM [Import]
expandSpecs Nothing                 = return []
expandSpecs (Just (Importing _ is)) = concat `liftM` mapM expandImport is
expandSpecs (Just (Hiding    _ is)) = concat `liftM` mapM expandHiding is

expandImport :: Import -> ExpandM [Import]
expandImport (Import             x) =               expandThing    x
expandImport (ImportTypeWith tc cs) = (:[]) `liftM` expandTypeWith tc cs
expandImport (ImportTypeAll     tc) = (:[]) `liftM` expandTypeAll  tc

expandHiding :: Import -> ExpandM [Import]
expandHiding (Import             x) = expandHide x
expandHiding (ImportTypeWith tc cs) = (:[]) `liftM` expandTypeWith tc cs
expandHiding (ImportTypeAll     tc) = (:[]) `liftM` expandTypeAll  tc

-- try to expand as type constructor
expandThing :: Ident -> ExpandM [Import]
expandThing tc = do
  tcEnv <- getTyConsEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandThing' tc $ Just [ImportTypeWith tc []]
    Nothing -> expandThing' tc Nothing

-- try to expand as function / data constructor
expandThing' :: Ident -> Maybe [Import] -> ExpandM [Import]
expandThing' f tcImport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  expand m f (Map.lookup f tyEnv) tcImport
  where
  expand :: ModuleIdent -> Ident
         -> Maybe ValueInfo -> Maybe [Import] -> ExpandM [Import]
  expand m e Nothing  Nothing   = report (errUndefinedEntity m e) >> return []
  expand _ _ Nothing  (Just tc) = return tc
  expand m e (Just v) maybeTc
    | isConstr v = case maybeTc of
        Nothing -> report (errImportDataConstr m e) >> return []
        Just tc -> return tc
    | otherwise  = return [Import e]

  isConstr (DataConstructor  _ _ _) = True
  isConstr (NewtypeConstructor _ _) = True
  isConstr (Value            _ _ _) = False
  isConstr (Label            _ _ _) = False

-- try to hide as type constructor
expandHide :: Ident -> ExpandM [Import]
expandHide tc = do
  tcEnv <- getTyConsEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandHide' tc $ Just [ImportTypeWith tc []]
    Nothing -> expandHide' tc Nothing

-- try to hide as function / data constructor
expandHide' :: Ident -> Maybe [Import] -> ExpandM [Import]
expandHide' f tcImport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  case Map.lookup f tyEnv of
    Just _  -> return $ Import f : fromMaybe [] tcImport
    Nothing -> case tcImport of
      Nothing -> report (errUndefinedEntity m f) >> return []
      Just tc -> return tc

expandTypeWith ::  Ident -> [Ident] -> ExpandM Import
expandTypeWith tc cs = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  ImportTypeWith tc `liftM` case Map.lookup tc tcEnv of
    Just (DataType     _ _                cs') ->
      mapM (checkConstr [c | Just (DataConstr c _ _) <- cs']) cs
    Just (RenamingType _ _ (DataConstr c _ _)) ->
      mapM (checkConstr [c]) cs
    Just (AliasType    _ _ (TypeRecord  fs _)) ->
      mapM (checkLabel [l | (l, _) <- fs] . renameLabel) cs
    Just (AliasType _ _ _) -> report (errNonDataType       tc) >> return []
    Nothing                -> report (errUndefinedEntity m tc) >> return []
  where
  checkConstr cs' c = do
    unless (c `elem` cs') $ report $ errUndefinedDataConstr tc c
    return c
  checkLabel ls' l  = do
    unless (l `elem` ls') $ report $ errUndefinedLabel tc l
    return l

expandTypeAll :: Ident -> ExpandM Import
expandTypeAll tc = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  ImportTypeWith tc `liftM` case Map.lookup tc tcEnv of
    Just (DataType     _ _                 cs) ->
      return [c | Just (DataConstr c _ _) <- cs]
    Just (RenamingType _ _ (DataConstr c _ _)) -> return [c]
    Just (AliasType    _ _ (TypeRecord  fs _)) -> return [l | (l, _) <- fs]
    Just (AliasType _ _ _) -> report (errNonDataType       tc) >> return []
    Nothing                -> report (errUndefinedEntity m tc) >> return []

errUndefinedEntity :: ModuleIdent -> Ident -> Message
errUndefinedEntity m x = posMessage x $ hsep $ map text
  [ "Module", moduleName m, "does not export", idName x ]

errUndefinedDataConstr :: Ident -> Ident -> Message
errUndefinedDataConstr tc c = posMessage c $ hsep $ map text
  [ idName c, "is not a data constructor of type", idName tc ]

errUndefinedLabel :: Ident -> Ident -> Message
errUndefinedLabel tc c = posMessage c $ hsep $ map text
  [ idName c, "is not a label of record type", idName tc ]

errNonDataType :: Ident -> Message
errNonDataType tc = posMessage tc $ hsep $ map text
  [ idName tc, "is not a data type" ]

errImportDataConstr :: ModuleIdent -> Ident -> Message
errImportDataConstr _ c = posMessage c $ hsep $ map text
  [ "Explicit import for data constructor", idName c ]

-- ---------------------------------------------------------------------------

-- After all modules have been imported, the compiler has to ensure that
-- all references to a data type use the same list of constructors.

importUnifyData :: CompilerEnv -> CompilerEnv
importUnifyData cEnv = cEnv { tyConsEnv = importUnifyData' $ tyConsEnv cEnv }

importUnifyData' :: TCEnv -> TCEnv
importUnifyData' tcEnv = fmap (setInfo allTyCons) tcEnv
  where
  setInfo tcs t   = fromJust $ Map.lookup (origName t) tcs
  allTyCons       = foldr (mergeData . snd) Map.empty $ allImports tcEnv
  mergeData t tcs =
    Map.insert tc (maybe t (fromJust . merge t) $ Map.lookup tc tcs) tcs
    where tc = origName t

-- ---------------------------------------------------------------------------

-- |
qualifyEnv :: Options -> CompilerEnv -> CompilerEnv
qualifyEnv opts env = expandValueEnv opts'
                    $ qualifyLocal env
                    $ foldl (flip importInterfaceIntf) initEnv
                    $ Map.elems
                    $ interfaceEnv env
  where initEnv = initCompilerEnv $ moduleIdent env
        opts' = opts { optExtensions = Records : optExtensions opts }

qualifyLocal :: CompilerEnv -> CompilerEnv -> CompilerEnv
qualifyLocal currentEnv initEnv = currentEnv
  { opPrecEnv = foldr bindQual   pEnv  $ localBindings $ opPrecEnv currentEnv
  , tyConsEnv = foldr bindQual   tcEnv $ localBindings $ tyConsEnv currentEnv
  , valueEnv  = foldr bindGlobal tyEnv $ localBindings $ valueEnv  currentEnv
  }
  where
    pEnv  = opPrecEnv initEnv
    tcEnv = tyConsEnv initEnv
    tyEnv = valueEnv  initEnv
    bindQual   (_, y) = qualBindTopEnv "Imports.qualifyEnv" (origName y) y
    bindGlobal (x, y)
      | hasGlobalScope x = bindQual (x, y)
      | otherwise        = bindTopEnv "Imports.qualifyEnv" x y

-- Importing an interface into another interface is somewhat simpler
-- because all entities are imported into the environment. In addition,
-- only a qualified import is necessary. Note that the hidden data types
-- are imported as well because they may be used in type expressions in
-- an interface.

importInterfaceIntf :: Interface -> CompilerEnv -> CompilerEnv
importInterfaceIntf i@(Interface m _ _) env = env
  { opPrecEnv = importEntities m True (const True) id mPEnv  $ opPrecEnv env
  , tyConsEnv = importEntities m True (const True) id mTCEnv $ tyConsEnv env
  , valueEnv  = importEntities m True (const True) id mTyEnv $ valueEnv  env
  }
  where
  mPEnv  = intfEnv bindPrec     i -- all operator precedences
  mTCEnv = intfEnv bindTCHidden i -- all type constructors
  mTyEnv = intfEnv bindTy       i -- all values

-- ---------------------------------------------------------------------------
-- Record stuff
-- ---------------------------------------------------------------------------

expandTCValueEnv :: Options -> CompilerEnv -> CompilerEnv
expandTCValueEnv opts env
  | enabled   = env' { tyConsEnv = tcEnv' }
  | otherwise = env
  where
  enabled = Records `elem` (optExtensions opts ++ extensions env)
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
  internalError "Imports.expandRecordTC"
expandRecordTC tcEnv (AliasType qid n ty) =
  AliasType qid n (expandRecords tcEnv ty)

expandValueEnv :: Options -> CompilerEnv -> CompilerEnv
expandValueEnv opts env
  | enabled   = env { valueEnv = tyEnv' }
  | otherwise = env
  where
  tcEnv   = tyConsEnv env
  tyEnv   = valueEnv env
  enabled = Records `elem` (optExtensions opts ++ extensions env)
  tyEnv'  = fmap (expandRecordTypes tcEnv) $ addImportedLabels m tyEnv
  m       = moduleIdent env

-- TODO: This is necessary as currently labels are unqualified.
-- Without this additional import the labels would no longer be known.
addImportedLabels :: ModuleIdent -> ValueEnv -> ValueEnv
addImportedLabels m tyEnv = foldr addLabelType tyEnv (allImports tyEnv)
  where
  addLabelType (_, lbl@(Label l r ty))
    = importTopEnv mid l' lbl
    -- the following is necessary to be available during generation
    -- of flat curry.
    . importTopEnv     mid (recSelectorId r l') sel
    . qualImportTopEnv mid (recSelectorId r l') sel
    . importTopEnv     mid (recUpdateId   r l') upd
    . qualImportTopEnv mid (recUpdateId   r l') upd
    where
    l' = unqualify l
    mid = fromMaybe m (qidModule r)
    sel = Value (qualRecSelectorId m r l') 1 ty
    upd = Value (qualRecUpdateId   m r l') 2 ty
  addLabelType _                       = id

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
