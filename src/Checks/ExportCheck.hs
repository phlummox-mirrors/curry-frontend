{- |
    Module      :  $Header$
    Description :  Check the export specification of a module
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a check of the export specification.
-}
module Checks.ExportCheck (exportCheck) where

import           Control.Monad              (liftM, unless)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List                  (nub, union)
import qualified Data.Map            as Map (Map, elems, empty, insertWith
                                            , toList)
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set (Set, empty, fromList, insert
                                            , member, toList)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Messages       (Message, internalError, posMessage)
import Base.TopEnv         (origName, localBindings, moduleImports)
import Base.Types          (DataConstr (..), Type (..))
import Base.Utils          (findMultiples)

import Env.ModuleAlias     (AliasEnv)
import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value           (ValueEnv, ValueInfo (..), lookupValue
                           , qualLookupValue)

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

  ambiErrs = map errMultipleType  (findMultiples exportedTypes)
          ++ map errMultipleName (findMultiples exportedValues)

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

-- |Expand export of type constructor / function
expandThing :: QualIdent -> ECM [Export]
expandThing tc = do
  tcEnv <- getTyConsEnv
  case qualLookupTC tc tcEnv of
    []  -> expandThing' tc Nothing
    [t] -> expandThing' tc (Just [ExportTypeWith (origName t) []])
    ts  -> report (errAmbiguousType tc ts) >> return []

-- |Expand export of data cons / function
expandThing' :: QualIdent -> Maybe [Export] -> ECM [Export]
expandThing' f tcExport = do
  tyEnv <- getValueEnv
  case qualLookupValue f tyEnv of
    []             -> justTcOr errUndefinedName
    [Value f' _ _] -> return $ Export f' : fromMaybe [] tcExport
    [_]            -> justTcOr errExportDataConstr
    _              -> do
      m <- getModuleIdent
      case qualLookupValue (qualQualify m f) tyEnv of
        []             -> justTcOr errUndefinedName
        [Value f' _ _] -> return $ Export f' : fromMaybe [] tcExport
        [_]            -> justTcOr errExportDataConstr
        fs             -> report (errAmbiguousName f fs) >> return []
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
                               return [ExportTypeWith (origName t)
                                        (map renameLabel nubCons)]
        | otherwise      -> report (errNonDataType tc) >> return []
    ts -> report (errAmbiguousType tc ts) >> return []
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
    ts  -> report (errAmbiguousType tc ts) >> return []

expandModule :: ModuleIdent -> ECM [Export]
expandModule em = do
  isLocal   <- (em ==)         `liftM` getModuleIdent
  isForeign <- (Set.member em) `liftM` getImportedModules
  locals    <- if isLocal   then expandLocalModule       else return []
  foreigns  <- if isForeign then expandImportedModule em else return []
  unless (isLocal || isForeign) $ report $ errModuleNotImported em
  return $ locals ++ foreigns

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

-- The expanded list of exported entities may contain duplicates.
-- These are removed by the function \texttt{joinExports}.
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
constrs (DataType     _ _ cs) = [c | Just (DataConstr c _ _) <- cs  ]
constrs (RenamingType _ _ nc) = [c |      (DataConstr c _ _) <- [nc]]
constrs (AliasType    _ _ _ ) = []

labels :: TypeInfo -> [Ident]
labels (AliasType _ _ (TypeRecord fs)) = map fst fs
labels _                               = []

isDataType :: TypeInfo -> Bool
isDataType (DataType     _ _ _) = True
isDataType (RenamingType _ _ _) = True
isDataType (AliasType    _ _ _) = False

isRecordType :: TypeInfo -> Bool
isRecordType (AliasType _ _ (TypeRecord _)) = True
isRecordType _                              = False

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errModuleNotImported :: ModuleIdent -> Message
errModuleNotImported m = posMessage m $ hsep $ map text
  ["Module", escModuleName m, "not imported"]

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "Type"

errUndefinedName :: QualIdent -> Message
errUndefinedName = errUndefined "Name"

errUndefined :: String -> QualIdent -> Message
errUndefined what tc = posMessage tc $ hsep $ map text
  ["Undefined", what, escQualName tc, "in export list"]

errMultipleType :: [Ident] -> Message
errMultipleType = errMultiple "type"

errMultipleName :: [Ident] -> Message
errMultipleName = errMultiple "name"

errMultiple :: String -> [Ident] -> Message
errMultiple _    []     = internalError
  "Checks.ExportCheck.errMultiple: empty list"
errMultiple what (i:is) = posMessage i $
  text "Multiple exports of" <+> text what <+> text (escName i) <+> text "at:"
  $+$ nest 2 (vcat (map showPos (i:is)))
  where showPos = text . showLine . idPosition

errAmbiguousType :: QualIdent -> [TypeInfo] -> Message
errAmbiguousType tc tcs = errAmbiguous "type" tc (map origName tcs)

errAmbiguousName :: QualIdent -> [ValueInfo] -> Message
errAmbiguousName x vs = errAmbiguous "name" x (map origName vs)

errAmbiguous :: String -> QualIdent -> [QualIdent] -> Message
errAmbiguous what qn qns = posMessage qn
  $   text "Ambiguous" <+> text what <+> text (escQualName qn)
  $+$ text "It could refer to:"
  $+$ nest 2 (vcat (map (text . escQualName) qns))

errExportDataConstr :: QualIdent -> Message
errExportDataConstr c = posMessage c $ hsep $ map text
  ["Data constructor", escQualName c, "outside type export in export list"]

errNonDataType :: QualIdent -> Message
errNonDataType tc = posMessage tc $ hsep $ map text
  [escQualName tc, "is not a data type"]

errUndefinedDataConstr :: QualIdent -> Ident -> Message
errUndefinedDataConstr tc c = posMessage c $ hsep $ map text
  [escName c, "is not a data constructor of type", escQualName tc]

errUndefinedLabel :: QualIdent -> Ident -> Message
errUndefinedLabel r l = posMessage l $ hsep $ map text
  [escName l, "is not a label of the record", escQualName r]
