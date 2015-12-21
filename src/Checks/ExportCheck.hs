{- |
    Module      :  $Header$
    Description :  Check the export specification of a module
    Copyright   :  (c) 1999 - 2004 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module implements a check and expansion of the export specification.
    Any errors in the specification are reported, and if there are no errors,
    the specification is expanded. The expansion does the following:
      * If there is no export specification, a specification exporting the
        entire module is generated.
      * Otherwise, (re)exports of modules are replaced by an export of all
        respective entities.
      * The export of a type with all constructors and fields is replaced
        by an enumeration of all constructors and fields.
      * The export of types without sub-entities is extended with an empty
        list of sub-entities.
-}
{-# LANGUAGE CPP #-}
module Checks.ExportCheck (exportCheck, expandExports) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>))
#endif
import           Control.Monad              (unless)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List                  (nub, union)
import qualified Data.Map            as Map (Map, elems, empty, insert
                                            , insertWith, lookup, toList)
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set (Set, empty, fromList, insert
                                            , member, toList)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Messages       (Message, internalError, posMessage)
import Base.TopEnv         (allEntities, origName, localBindings, moduleImports)
import Base.Types          ( DataConstr (..), ExistTypeScheme (..), Type (..)
                           , TypeScheme (..), arrowBase, constrIdent, recLabels)
import Base.Utils          (findMultiples)

import Env.ModuleAlias     (AliasEnv)
import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTCUnique)
import Env.Value           (ValueEnv, ValueInfo (..), qualLookupValueUnique)

-- ---------------------------------------------------------------------------
-- Check and expansion of the export statement
-- ---------------------------------------------------------------------------

expandExports :: ModuleIdent -> AliasEnv -> TCEnv -> ValueEnv
              -> Maybe ExportSpec -> ExportSpec
expandExports m aEnv tcEnv tyEnv spec = Exporting (exportPos spec) es
  where
  exportPos (Just (Exporting p _)) = p
  exportPos Nothing                = NoPos

  es = fst (checkAndExpand m aEnv tcEnv tyEnv spec)

exportCheck :: ModuleIdent -> AliasEnv -> TCEnv -> ValueEnv
            -> Maybe ExportSpec -> [Message]
exportCheck m aEnv tcEnv tyEnv spec = case errs of
  [] -> checkNonUniqueness es
  ms -> ms
  where
  (es, errs) = checkAndExpand m aEnv tcEnv tyEnv spec

checkAndExpand :: ModuleIdent -> AliasEnv -> TCEnv -> ValueEnv
               -> Maybe ExportSpec -> ([Export], [Message])
checkAndExpand m aEnv tcEnv tyEnv spec
  = runECM ((joinExports . canonExports tcEnv) <$> expandSpec spec) initState
  where
  initState  = ECState m imported tcEnv tyEnv []
  imported   = Set.fromList (Map.elems aEnv)

-- Check whether two entities of the same kind (type or constructor/function)
-- share the same unqualified name, which is not allowed since they could
-- not be uniquely resolved at their usage.
-- For instance, consider the following module
-- @
-- module M (Bool, Prelude.Bool) where
-- data Bool = False | True
-- @
-- If this export would be allowed, in a module @M1@ as follows
-- @
-- module M1 where
-- import M (Bool)
-- @
-- the type @Bool@ could not be resolved uniquely to its definition.
-- Naturally, the same applies for constructors or functions.
checkNonUniqueness :: [Export] -> [Message]
checkNonUniqueness es = map errMultipleType (findMultiples types )
                     ++ map errMultipleName (findMultiples values)
  where
  types  = [ unqualify tc | ExportTypeWith tc _  <- es ]
  values = [ c            | ExportTypeWith _  cs <- es, c <- cs ]
        ++ [ unqualify f  | Export f <- es ]

-- -----------------------------------------------------------------------------
-- Expansion + Check
-- -----------------------------------------------------------------------------

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
-- specifications of the form @T(..)@ into @T(C_1,...,C_m,l_1,...,l_n)@,
-- where @C_1,...,C_m@ are the data constructors of type @T@ and @l_1,...,l_n@
-- its field labels, and replaces an export specification
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
expandSpec (Just (Exporting _ es)) = concat <$> mapM expandExport es

-- |Expand single export
expandExport :: Export -> ECM [Export]
expandExport (Export             x) = expandThing x
expandExport (ExportTypeWith tc cs) = expandTypeWith tc cs
expandExport (ExportTypeAll     tc) = expandTypeAll tc
expandExport (ExportModule      em) = expandModule em

-- |Expand export of type constructor / function
expandThing :: QualIdent -> ECM [Export]
expandThing tc = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  case qualLookupTCUnique m tc tcEnv of
    []  -> expandThing' tc Nothing
    [t] -> expandThing' tc (Just [ExportTypeWith (origName t) []])
    ts  -> report (errAmbiguousType tc ts) >> return []

-- |Expand export of data cons / function
expandThing' :: QualIdent -> Maybe [Export] -> ECM [Export]
expandThing' f tcExport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  case qualLookupValueUnique m f tyEnv of
    []             -> justTcOr errUndefinedName
    [Value f' _ _] -> return $ Export f' : fromMaybe [] tcExport
    [Label l  _ (ForAll _ (TypeArrow (TypeConstructor tc _) _))] -> do
      report $ errExportLabel f tc
      return $ Export l  : fromMaybe [] tcExport
    [c]            -> justTcOr $ flip errExportDataConstr $ getTc c
    fs             -> report (errAmbiguousName f fs) >> return []
  where
  justTcOr errFun = case tcExport of
    Nothing -> report (errFun f) >> return []
    Just tc -> return tc

  getTc (DataConstructor  _ _ _ (ForAllExist _ _ ty)) = getTc' ty
  getTc (NewtypeConstructor _ _ (ForAllExist _ _ ty)) = getTc' ty
  getTc (Label _ _ (ForAll _ (TypeArrow (TypeConstructor tc _) _))) = tc
  getTc _ = internalError "ExportCheck.getTc"

  getTc' ty = let (TypeConstructor tc _) = arrowBase ty in tc

-- |Expand type constructor with explicit data constructors and record labels
expandTypeWith :: QualIdent -> [Ident] -> ECM [Export]
expandTypeWith tc xs = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  case qualLookupTCUnique m tc tcEnv of
    [] -> report (errUndefinedType tc) >> return []
    [t@(DataType _ _ cs)]    -> do
      mapM_ (checkElement (visibleElems cs)) xs'
      return [ExportTypeWith (origName t) xs']
    [t@(RenamingType _ _ c)] -> do
      mapM_ (checkElement (visibleElems [c])) xs'
      return [ExportTypeWith (origName t) xs']
    [_] -> report (errNonDataType tc)      >> return []
    ts  -> report (errAmbiguousType tc ts) >> return []
  where
  xs' = nub xs
  -- check if given identifier is constructor or label of type tc
  checkElement cs' c = do
    unless (c `elem` cs') $ report $ errUndefinedElement tc c
    return c

-- |Expand type constructor with all data constructors and record labels
expandTypeAll :: QualIdent -> ECM [Export]
expandTypeAll tc = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  case qualLookupTCUnique m tc tcEnv of
    [] -> report (errUndefinedType tc) >> return []
    [t@(DataType     _ _ _)] -> return $ [exportType t]
    [t@(RenamingType _ _ _)] -> return $ [exportType t]
    [_] -> report (errNonDataType tc)      >> return []
    ts  -> report (errAmbiguousType tc ts) >> return []

expandModule :: ModuleIdent -> ECM [Export]
expandModule em = do
  isLocal   <- (em ==)         <$> getModuleIdent
  isForeign <- (Set.member em) <$> getImportedModules
  locals    <- if isLocal   then expandLocalModule       else return []
  foreigns  <- if isForeign then expandImportedModule em else return []
  unless (isLocal || isForeign) $ report $ errModuleNotImported em
  return $ locals ++ foreigns

expandLocalModule :: ECM [Export]
expandLocalModule = do
  tcEnv <- getTyConsEnv
  tyEnv <- getValueEnv
  return $
       [ exportType t | (_, t) <- localBindings tcEnv ]
    ++ [ Export f' | (f, Value f' _ _) <- localBindings tyEnv, hasGlobalScope f ]
    ++ [ Export l' | (l, Label l' _ _) <- localBindings tyEnv, hasGlobalScope l ]

-- |Expand a module export
expandImportedModule :: ModuleIdent -> ECM [Export]
expandImportedModule m = do
  tcEnv <- getTyConsEnv
  tyEnv <- getValueEnv
  return $ [exportType t |       (_, t) <- moduleImports m tcEnv]
        ++ [Export f | (_, Value f _ _) <- moduleImports m tyEnv]
        ++ [Export l | (_, Label l _ _) <- moduleImports m tyEnv]

exportType :: TypeInfo -> Export
exportType t = ExportTypeWith tc xs
  where tc = origName t
        xs = elements t

-- -----------------------------------------------------------------------------
-- Canonicalization and joining of exports
-- -----------------------------------------------------------------------------

-- In contrast to Haskell, the export of field labels and record constructors
-- without their types is NOT allowed.
-- Thus, given the declaration @data T a = C { l :: a }@
-- the label @l@ and the constructor @C@ can only be exported together with the
-- type @T@, i.e., @(T(C,l))@.
-- Since record update operations are desugared to case expressions matching the
-- corresponding constructors of the record, the export of a label without its
-- type could result in a type error, when it is used for an update operation in
-- another module.

canonExports :: TCEnv -> [Export] -> [Export]
canonExports tcEnv es = map (canonExport (canonLabels tcEnv es)) es

canonExport :: Map.Map QualIdent Export -> Export -> Export
canonExport ls (Export x)             = fromMaybe (Export x) (Map.lookup x ls)
canonExport _  (ExportTypeWith tc xs) = ExportTypeWith tc xs
canonExport _  e                      = internalError $
  "Checks.ExportCheck.canonExport: " ++ show e

canonLabels :: TCEnv -> [Export] -> Map.Map QualIdent Export
canonLabels tcEnv es = foldr bindLabels Map.empty (allEntities tcEnv)
  where
    tcs = [tc | ExportTypeWith tc _ <- es]
    bindLabels t ls
      | tc' `elem` tcs = foldr (bindLabel tc') ls (elements t)
      | otherwise     = ls
        where
          tc'            = origName t
          bindLabel tc x = Map.insert (qualifyLike tc x) (ExportTypeWith tc [x])

-- The expanded list of exported entities may contain duplicates. These
-- are removed by the function joinExports. In particular, this
-- function removes any field labels from the list of exported values
-- which are also exported along with their types.

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

elements :: TypeInfo -> [Ident]
elements (DataType    _ _ cs) = visibleElems cs
elements (RenamingType _ _ c) = visibleElems [c]
elements (AliasType    _ _ _) = []

-- get visible constructor and label identifiers for given constructor
visibleElems :: [DataConstr] -> [Ident]
visibleElems cs = map constrIdent cs ++ (nub (concatMap recLabels cs))

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errModuleNotImported :: ModuleIdent -> Message
errModuleNotImported m = posMessage m $ hsep $ map text
  ["Module", escModuleName m, "not imported"]

errUndefinedType :: QualIdent -> Message
errUndefinedType = errUndefined "Type"

errUndefinedElement :: QualIdent -> Ident -> Message
errUndefinedElement tc c = posMessage c $ hsep $ map text
  [ idName c, "is not a constructor or label of type ", qualName tc ]

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

errExportDataConstr :: QualIdent -> QualIdent -> Message
errExportDataConstr c tc = errOutsideTypeExport "Data constructor" c tc

errNonDataType :: QualIdent -> Message
errNonDataType tc = posMessage tc $ hsep $ map text
  [escQualName tc, "is not a data type"]

errExportLabel :: QualIdent -> QualIdent -> Message
errExportLabel l tc = errOutsideTypeExport "Label" l tc

errOutsideTypeExport :: String -> QualIdent -> QualIdent -> Message
errOutsideTypeExport what q tc = posMessage q
  $   text what <+> text (escQualName q)
         <+> text "outside type export in export list"
  $+$ text "Use `" <> text (qualName tc) <+> parens (text (qualName q))
  <>  text "' instead"
