module Checks.ExportCheck (exportCheck) where

import Data.List (nub, union)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.Messages
import Base.TopEnv
import Base.Types
import Base.Utils (findDouble)

import Env.TypeConstructors
import Env.Value

import CompilerEnv

-- ---------------------------------------------------------------------------
-- Check and expansion of the export statement
-- ---------------------------------------------------------------------------

exportCheck :: CompilerEnv -> Module -> Module
exportCheck env (Module m es is ds) = case findDouble exportedTypes of
  Just tc -> errorMessage $ errAmbiguousExportType tc
  Nothing -> case findDouble exportedValues of
    Just v  -> errorMessage $ errAmbiguousExportValue v
    Nothing -> Module m (Just (Exporting NoPos expandedExports)) is ds
  where
  (tcEnv, tyEnv) = (tyConsEnv env, valueEnv env)
  expandedExports = joinExports
                  $ maybe (expandLocalModule          tcEnv tyEnv)
                          (expandSpecs importedMods m tcEnv tyEnv)
                          es
  importedMods   = Set.fromList
                   [fromMaybe m' asM | ImportDecl _ m' _ asM _ <- is]
  exportedTypes  = [unqualify tc | ExportTypeWith tc _ <- expandedExports]
  exportedValues = [c | ExportTypeWith _ cs <- expandedExports, c <- cs]
                ++ [unqualify f | Export f <- expandedExports]

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
expandSpecs :: Set.Set ModuleIdent -> ModuleIdent -> TCEnv -> ValueEnv
            -> ExportSpec -> [Export]
expandSpecs ms m tcEnv tyEnv (Exporting _ es) =
  concatMap (expandExport ms m tcEnv tyEnv) es

-- |Expand single export
expandExport :: Set.Set ModuleIdent -> ModuleIdent -> TCEnv -> ValueEnv
             -> Export -> [Export]
expandExport _  m tcEnv tyEnv (Export x)
  = expandThing m tcEnv tyEnv x
expandExport _  m tcEnv _     (ExportTypeWith tc cs)
  = expandTypeWith m tcEnv tc cs
expandExport _  m tcEnv tyEnv (ExportTypeAll tc)
  = expandTypeAll m tyEnv tcEnv tc
expandExport ms m tcEnv tyEnv (ExportModule m')
  | m' == m
  = (if m' `Set.member` ms then expandModule tcEnv tyEnv m' else []) -- TODO: Can this happen???
              ++ expandLocalModule tcEnv tyEnv
  | m' `Set.member` ms
  = expandModule tcEnv tyEnv m'
  | otherwise
  = errorMessage $ errModuleNotImported m'

-- |Expand export of type cons / data cons / function
expandThing :: ModuleIdent -> TCEnv -> ValueEnv -> QualIdent -> [Export]
expandThing m tcEnv tyEnv tc = case qualLookupTC tc tcEnv of
  []  -> expandThing' m tyEnv tc Nothing
  [t] -> expandThing' m tyEnv tc (Just [ExportTypeWith (origName t) []])
  _   -> errorMessage $ errAmbiguousType tc

-- |Expand export of data cons / function
expandThing' :: ModuleIdent -> ValueEnv -> QualIdent -> Maybe [Export]
             -> [Export]
expandThing' m tyEnv f tcExport = case qualLookupValue f tyEnv of
  []             -> fromMaybe (errorMessage $ errUndefinedEntity f) tcExport
  [Value f' _ _] -> Export f' : fromMaybe [] tcExport
  [_]            -> fromMaybe (errorMessage $ errExportDataConstr f) tcExport
  _              -> case qualLookupValue (qualQualify m f) tyEnv of
    []             -> fromMaybe (errorMessage $ errUndefinedEntity f) tcExport
    [Value f' _ _] -> Export f' : fromMaybe [] tcExport
    [_]            -> fromMaybe (errorMessage $ errExportDataConstr f) tcExport
    _              -> errorMessage $ errAmbiguousName f

-- |Expand type constructor with explicit data constructors
expandTypeWith :: ModuleIdent -> TCEnv -> QualIdent -> [Ident] -> [Export]
expandTypeWith _ tcEnv tc cs = case qualLookupTC tc tcEnv of
  [] -> errorMessage $ errUndefinedType tc
  [t] | isDataType t   -> [ ExportTypeWith (origName t)
                          $ map (checkConstr $ constrs t) $ nub cs]
      | isRecordType t -> [ ExportTypeWith (origName t)
                          $ map (checkLabel  $ labels  t) $ nub cs]
      | otherwise      -> errorMessage $ errNonDataType tc
  _  -> errorMessage $ errAmbiguousType tc
  where
    checkConstr cs' c
      | c `elem` cs' = c
      | otherwise    = errorMessage $ errUndefinedDataConstr tc c
    checkLabel ls l
      | l' `elem` ls = l'
      | otherwise    = errorMessage $ errUndefinedLabel tc l
      where l' = renameLabel l

-- |Expand type constructor with all data constructors
expandTypeAll :: ModuleIdent -> ValueEnv -> TCEnv -> QualIdent -> [Export]
expandTypeAll _ tyEnv tcEnv tc = case qualLookupTC tc tcEnv of
  [] -> errorMessage $ errUndefinedType tc
  [t] | isDataType t   -> [exportType tyEnv t]
      | isRecordType t -> exportRecord t
      | otherwise      -> errorMessage $ errNonDataType tc
  _ -> errorMessage $ errAmbiguousType tc

expandLocalModule :: TCEnv -> ValueEnv -> [Export]
expandLocalModule tcEnv tyEnv =
  [exportType tyEnv t | (_,t) <- localBindings tcEnv] ++
  [Export f' | (f,Value f' _ _) <- localBindings tyEnv, f == unRenameIdent f]

-- |Expand a module export
expandModule :: TCEnv -> ValueEnv -> ModuleIdent -> [Export]
expandModule tcEnv tyEnv m =
  [exportType tyEnv t | (_,t) <- moduleImports m tcEnv] ++
  [Export f | (_,Value f _ _) <- moduleImports m tyEnv]

exportType :: ValueEnv -> TypeInfo -> Export
exportType tyEnv t
  | isRecordType t -- = ExportTypeWith (origName t) (labels t)
  = let ls = labels t
        r  = origName t
    in case lookupValue (head ls) tyEnv of
      [Label _ r' _] -> if r == r' then ExportTypeWith r ls
                                   else ExportTypeWith r []
      _              -> internalError "Exports.exportType"
  | otherwise = ExportTypeWith (origName t) (constrs t)

exportRecord :: TypeInfo -> [Export]
exportRecord t = [ExportTypeWith (origName t) $ labels t]

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
joinType _                        _ = internalError
  "Exports.joinType: no pattern match" -- TODO

joinFun :: Export -> Set.Set QualIdent -> Set.Set QualIdent
joinFun (Export           f) fs = f `Set.insert` fs
joinFun (ExportTypeWith _ _) fs = fs
joinFun _                     _ = internalError
  "Exports.joinFun: no pattern match" -- TODO

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

isDataType :: TypeInfo -> Bool
isDataType (DataType     _ _ _) = True
isDataType (RenamingType _ _ _) = True
isDataType (AliasType    _ _ _) = False

isRecordType :: TypeInfo -> Bool
isRecordType (AliasType _ _ (TypeRecord _ _)) = True
isRecordType _                                = False

constrs :: TypeInfo -> [Ident]
constrs (DataType _ _ cs)  = [c | Just (DataConstr c _ _) <- cs]
constrs (RenamingType _ _ (DataConstr c _ _)) = [c]
constrs (AliasType _ _ _)  = []

labels :: TypeInfo -> [Ident]
labels (AliasType _ _ (TypeRecord fs _)) = map fst fs
labels _                                 = []

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
errModuleNotImported m = toMessage (positionOfModuleIdent m) $
  "Module " ++ moduleName m ++ " not imported"

errAmbiguousExportType :: Ident -> Message
errAmbiguousExportType x = posErr x $ "Ambiguous export of type " ++ name x

errAmbiguousExportValue :: Ident -> Message
errAmbiguousExportValue x = posErr x $ "Ambiguous export of " ++ name x

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
