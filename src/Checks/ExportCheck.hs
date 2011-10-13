module Checks.ExportCheck (exportCheck) where

import Control.Monad (liftM, unless)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import Data.List (nub, union)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.Messages (Message, internalError, mposErr, posErr, qposErr)
import Base.TopEnv
import Base.Types
import Base.Utils (findMultiples)

import Env.ModuleAlias
import Env.TypeConstructors
import Env.Value

-- ---------------------------------------------------------------------------
-- Check and expansion of the export statement
-- ---------------------------------------------------------------------------

exportCheck :: ModuleIdent -> AliasEnv -> TCEnv -> ValueEnv
            -> Maybe ExportSpec -> (Maybe ExportSpec, [Message])
exportCheck m aEnv tcEnv tyEnv spec = case expErrs of
  [] -> (Just $ Exporting NoPos exports, ambiErrs)
  ms -> (spec, ms)
  where
  (exports, expErrs) = runECM (joinExports `liftM` expandSpec spec) initState
  initState          = ECState m imported tcEnv tyEnv []
  imported           = Set.fromList $ Map.elems aEnv

  ambiErrs = map errMultipleExportType  (findMultiples exportedTypes)
          ++ map errMultipleExportValue (findMultiples exportedValues)

  exportedTypes  = [unqualify tc | ExportTypeWith tc _ <- exports]
  exportedValues = [c | ExportTypeWith _ cs <- exports, c <- cs]
                ++ [unqualify f | Export f <- exports]

data ECState = ECState
  { moduleIdent  :: ModuleIdent
  , importedMods :: Set.Set ModuleIdent
  , tyConsEnv    :: TCEnv
  , valueEnv     :: ValueEnv
  , errors       :: [Message]
  }

type ECM a = S.State ECState a

runECM :: ECM a -> ECState -> (a, [Message])
runECM ecm s = let (a, s') = S.runState ecm s in (a, reverse $ errors s')

getModuleIdent :: ECM ModuleIdent
getModuleIdent = S.gets moduleIdent

getImportedModules :: ECM (Set.Set ModuleIdent)
getImportedModules = S.gets importedMods

getTyConsEnv :: ECM TCEnv
getTyConsEnv = S.gets tyConsEnv

getValueEnv :: ECM ValueEnv
getValueEnv = S.gets valueEnv

report :: Message -> ECM ()
report err = S.modify (\ s -> s { errors = err : errors s })

-- While checking all export specifications, the compiler expands
-- specifications of the form @T(..)@ into @T(C_1,...,C_n)@,
-- where @C_1,...,C_n@ are the data constructors or the record labels of
-- type @T@, and replaces an export specification
-- @module M@ by specifications for all entities which are defined
-- in module @M@ and imported into the current module with their
-- unqualified name. In order to distinguish exported type constructors
-- from exported functions, the former are translated into the equivalent
-- form @T()@. Note that the export specification @x@ may
-- export a type constructor @x@ /and/ a global function
-- @x@ at the same time.
--
-- /Note:/ This frontend allows redeclaration and export of imported
-- identifiers.

-- |Expand export specification
expandSpec :: Maybe ExportSpec -> ECM [Export]
expandSpec Nothing                 = expandLocalModule
expandSpec (Just (Exporting _ es)) = concat `liftM` mapM expandExport es

-- |Expand single export
expandExport :: Export -> ECM [Export]
expandExport (Export             x) = expandThing x
expandExport (ExportTypeWith tc cs) = expandTypeWith tc cs
expandExport (ExportTypeAll     tc) = expandTypeAll tc
expandExport (ExportModule      em) = expandModule em

-- |Expand export of type cons / data cons / function
expandThing :: QualIdent -> ECM [Export]
expandThing tc = do
  tcEnv <- getTyConsEnv
  case qualLookupTC tc tcEnv of
    []  -> expandThing' tc Nothing
    [t] -> expandThing' tc (Just [ExportTypeWith (origName t) []])
    _   -> report (errAmbiguousType tc) >> return []

-- |Expand export of data cons / function
expandThing' :: QualIdent -> Maybe [Export] -> ECM [Export]
expandThing' f tcExport = do
  tyEnv <- getValueEnv
  case qualLookupValue f tyEnv of
    []             -> justTcOr errUndefinedEntity
    [Value f' _ _] -> return $ Export f' : fromMaybe [] tcExport
    [_]            -> justTcOr errExportDataConstr
    _              -> do
      m <- getModuleIdent
      case qualLookupValue (qualQualify m f) tyEnv of
        []             -> justTcOr errUndefinedEntity
        [Value f' _ _] -> return $ Export f' : fromMaybe [] tcExport
        [_]            -> justTcOr errExportDataConstr
        _              -> report (errAmbiguousName f) >> return []
  where justTcOr errFun = case tcExport of
          Nothing -> report (errFun f) >> return []
          Just tc -> return tc

-- |Expand type constructor with explicit data constructors
expandTypeWith :: QualIdent -> [Ident] -> ECM [Export]
expandTypeWith tc cs = do
  tcEnv <- getTyConsEnv
  case qualLookupTC tc tcEnv of
    [] -> report (errUndefinedType tc) >> return []
    [t] | isDataType   t -> do mapM_ (checkConstr $ constrs t) nubCons
                               return [ExportTypeWith (origName t) nubCons]
        | isRecordType t -> do mapM_ (checkLabel  $ labels  t) nubCons
                               return [ExportTypeWith (origName t) (map renameLabel nubCons)]
        | otherwise      -> report (errNonDataType tc) >> return []
    _  -> report (errAmbiguousType tc) >> return []
  where
  nubCons = nub cs
  checkConstr cs' c = unless (c `elem` cs')
                      (report $ errUndefinedDataConstr tc c)
  checkLabel ls l   = unless (renameLabel l `elem` ls)
                      (report $ errUndefinedLabel tc l)

-- |Expand type constructor with all data constructors
expandTypeAll :: QualIdent -> ECM [Export]
expandTypeAll tc = do
  tcEnv <- getTyConsEnv
  case qualLookupTC tc tcEnv of
    []  -> report (errUndefinedType tc) >> return []
    [t] -> do
      tyEnv <- getValueEnv
      if isDataType t || isRecordType t
        then return [exportType tyEnv t]
        else report (errNonDataType tc) >> return []
    _   -> report (errAmbiguousType tc) >> return []

expandModule :: ModuleIdent -> ECM [Export]
expandModule em = do
  m        <- getModuleIdent
  locals   <- if em == m then expandLocalModule else return []
  reexport <- do
    knownModules <- getImportedModules
    if em `Set.member` knownModules
      then expandImportedModule em
      else report (errModuleNotImported em) >> return []
  return $ locals ++ reexport

expandLocalModule :: ECM [Export]
expandLocalModule = do
  tcEnv <- getTyConsEnv
  tyEnv <- getValueEnv
  return $ [exportType tyEnv t | (_, t) <- localBindings tcEnv] ++
    [Export f' | (f, Value f' _ _) <- localBindings tyEnv, f == unRenameIdent f]

-- |Expand a module export
expandImportedModule :: ModuleIdent -> ECM [Export]
expandImportedModule m = do
  tcEnv <- getTyConsEnv
  tyEnv <- getValueEnv
  return $ [exportType tyEnv t | (_, t) <- moduleImports m tcEnv]
        ++ [Export f | (_, Value f _ _) <- moduleImports m tyEnv]

exportType :: ValueEnv -> TypeInfo -> Export
exportType tyEnv t
  | isRecordType t
  = let ls = labels t
        r  = origName t
    in  case lookupValue (head ls) tyEnv of
      [Label _ r' _]  -> if r == r' then ExportTypeWith r ls
                                    else ExportTypeWith r []
      _               -> internalError "Exports.exportType"
  | otherwise      = ExportTypeWith (origName t) (constrs t)

-- The expanded list of exported entities may contain duplicates. These
-- are removed by the function \texttt{joinExports}.

joinExports :: [Export] -> [Export]
joinExports es =  [ExportTypeWith tc cs | (tc, cs) <- joinedTypes]
               ++ [Export f             | f        <- joinedFuncs]
  where joinedTypes = Map.toList $ foldr joinType Map.empty es
        joinedFuncs = Set.toList $ foldr joinFun  Set.empty es

joinType :: Export -> Map.Map QualIdent [Ident] -> Map.Map QualIdent [Ident]
joinType (Export             _) tcs = tcs
joinType (ExportTypeWith tc cs) tcs = Map.insertWith union tc cs tcs
joinType export                   _ = internalError $
  "Checks.ExportCheck.joinType: " ++ show export

joinFun :: Export -> Set.Set QualIdent -> Set.Set QualIdent
joinFun (Export           f) fs = f `Set.insert` fs
joinFun (ExportTypeWith _ _) fs = fs
joinFun export                _ = internalError $
  "Checks.ExportCheck.joinFun: " ++ show export

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

constrs :: TypeInfo -> [Ident]
constrs (DataType _ _ cs)  = [c | Just (DataConstr c _ _) <- cs]
constrs (RenamingType _ _ (DataConstr c _ _)) = [c]
constrs (AliasType _ _ _)  = []

labels :: TypeInfo -> [Ident]
labels (AliasType _ _ (TypeRecord fs _)) = map fst fs
labels _                                 = []

isDataType :: TypeInfo -> Bool
isDataType (DataType     _ _ _) = True
isDataType (RenamingType _ _ _) = True
isDataType (AliasType    _ _ _) = False

isRecordType :: TypeInfo -> Bool
isRecordType (AliasType _ _ (TypeRecord _ _)) = True
isRecordType _                                = False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUndefinedEntity :: QualIdent -> Message
errUndefinedEntity x = qposErr x $
  "Entity " ++ qualName x ++ " in export list is not defined"

errUndefinedType :: QualIdent -> Message
errUndefinedType tc = qposErr tc $
  "Type " ++ qualName tc ++ " in export list is not defined"

errModuleNotImported :: ModuleIdent -> Message
errModuleNotImported m = mposErr m $
  "Module " ++ moduleName m ++ " not imported"

errMultipleExportType :: [Ident] -> Message
errMultipleExportType []     = internalError
  "Checks.ExportCheck.errMultipleExportType: empty list"
errMultipleExportType (i:is) = posErr i $
  "Multiple exports of type " ++ name i ++ " at:\n"
  ++ unlines (map showPos (i:is))
  where showPos = ("    " ++) . showLine . positionOfIdent

errMultipleExportValue :: [Ident] -> Message
errMultipleExportValue []     = internalError
  "Checks.ExportCheck.errMultipleExportValue: empty list"
errMultipleExportValue (i:is) = posErr i $
  "Multiple exports of " ++ name i ++ " at:\n"
  ++ unlines (map showPos (i:is))
  where showPos = ("    " ++) . showLine . positionOfIdent

errAmbiguousType :: QualIdent -> Message
errAmbiguousType tc = qposErr tc $ "Ambiguous type " ++ qualName tc

errAmbiguousName :: QualIdent -> Message
errAmbiguousName x = qposErr x $ "Ambiguous name " ++ qualName x

errExportDataConstr :: QualIdent -> Message
errExportDataConstr c = qposErr c $
  "Data constructor " ++ qualName c ++ " in export list"

errNonDataType :: QualIdent -> Message
errNonDataType tc = qposErr tc $ qualName tc ++ " is not a data type"

errUndefinedDataConstr :: QualIdent -> Ident -> Message
errUndefinedDataConstr tc c = posErr c $
  name c ++ " is not a data constructor of type " ++ qualName tc

errUndefinedLabel :: QualIdent -> Ident -> Message
errUndefinedLabel r l = posErr l $
  name l ++ " is not a label of the record " ++ qualName r
