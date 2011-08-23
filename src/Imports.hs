{- |
    Module      :  $Header$
    Description :  Importing interface declarations
    Copyright   :  (c) 2000-2003, Wolfgang Lux
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importModules' to bring the imported
    entities into the module's scope, and the function 'qualifyEnv' to
    qualify the environment prior to computing the export interface.
-}
module Imports (importModules, qualifyEnv) where

import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Curry.Base.Position
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryTypes (toQualType, toQualTypes)
import Base.Messages (internalError, errorAt')
import Base.Types

import Env.Arity
import Env.Interface
import Env.ModuleAlias
import Env.OpPrec
import Env.TopEnv
import Env.TypeConstructors
import Env.Value

import CompilerEnv
import CompilerOpts
import Records (importLabels, recordExpansion1, recordExpansion2)

-- ---------------------------------------------------------------------------
-- Interface
-- ---------------------------------------------------------------------------

-- |The function 'importModules' brings the declarations of all
-- imported interfaces into scope for the current module.
importModules :: Options -> ModuleIdent -> InterfaceEnv
              -> [ImportDecl] -> CompilerEnv
importModules opts mid iEnv decls = recordExpansion1 opts
                                  $ importUnifyData
                                  $ foldl importModule initEnv decls
  where
    initEnv = (initCompilerEnv mid)
      { aliasEnv     = importAliases     decls -- import module aliases
      , labelEnv     = importLabels iEnv decls -- import record labels
      , interfaceEnv = iEnv                    -- imported interfaces
      }
    importModule env (ImportDecl _ m q asM is) = case Map.lookup m iEnv of
      Just intf -> importInterface (fromMaybe m asM) q is intf env
      Nothing   -> internalError $ "Imports.importModules: no interface for "
                                   ++ show m

-- |
qualifyEnv :: Options -> InterfaceEnv -> CompilerEnv -> CompilerEnv
qualifyEnv opts iEnv env = recordExpansion2 opts
                         $ qualifyLocal env
                         $ foldl (flip importInterfaceIntf) initEnv
                         $ Map.elems iEnv
  where initEnv = initCompilerEnv $ moduleIdent env

-- ---------------------------------------------------------------------------
-- Importing an interface into the module
-- ---------------------------------------------------------------------------

-- Four kinds of environments are computed from the interface:
--
-- 1. The operator precedences
-- 2. The type constructors
-- 3. The types of the data constructors and functions (values)
-- 4. The arity for each function and constructor
--
-- Note that the original names of all entities defined in the imported module
-- are qualified appropriately. The same is true for type expressions.

type IdentMap    = Map.Map Ident

type ExpPEnv     = IdentMap PrecInfo
type ExpTCEnv    = IdentMap TypeInfo
type ExpValueEnv = IdentMap ValueInfo
type ExpArityEnv = IdentMap ArityInfo

-- When an interface is imported, the compiler first transforms the
-- interface into these environments. If an import specification is
-- present, the environments are restricted to only those entities which
-- are included in the specification or not hidden by it, respectively.
-- The resulting environments are then imported into the current module
-- using either a qualified import (if the module is imported qualified)
-- or both a qualified and an unqualified import (non-qualified import).

importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec -> Interface
                -> CompilerEnv -> CompilerEnv
importInterface m q is i env = env
  { opPrecEnv = importEntities m q vs id              mPEnv  $ opPrecEnv env
  , tyConsEnv = importEntities m q ts (importData vs) mTCEnv $ tyConsEnv env
  , valueEnv  = importEntities m q vs id              mTyEnv $ valueEnv  env
  , arityEnv  = importEntities m q as id              mAEnv  $ arityEnv  env
  }
  where mPEnv  = intfEnv bindPrec i -- all operator precedences
        mTCEnv = intfEnv bindTC   i -- all type constructors
        mTyEnv = intfEnv bindTy   i -- all values
        mAEnv  = intfEnv bindA    i -- all arities
        expandedSpec = maybe [] (expandSpecs m mTCEnv mTyEnv) is -- all imported type constructors / values
        ts = isVisible is (Set.fromList $ foldr addType  [] expandedSpec)
        vs = isVisible is (Set.fromList $ foldr addValue [] expandedSpec)
        as = isVisible is (Set.fromList $ foldr addArity [] expandedSpec)

isVisible :: Maybe ImportSpec -> Set.Set Ident -> Ident -> Bool
isVisible (Just (Importing _ _)) xs = (`Set.member`    xs)
isVisible (Just (Hiding    _ _)) xs = (`Set.notMember` xs)
isVisible Nothing                _  = const True

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
bindPrec m (IInfixDecl _ fix p op) =
  Map.insert (unqualify op) (PrecInfo (qualQualify m op) (OpPrec fix p))
bindPrec _ _ = id

bindTCHidden :: ModuleIdent -> IDecl -> ExpTCEnv -> ExpTCEnv
bindTCHidden m (HidingDataDecl _ tc tvs) =
  bindType DataType m (qualify tc) tvs []
bindTCHidden m d = bindTC m d

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
bindTy m (IDataDecl _ tc tvs cs) =
  flip (foldr (bindConstr m tc' tvs (constrType tc' tvs))) (catMaybes cs)
  where tc' = qualQualify m tc

bindTy m (INewtypeDecl _ tc tvs nc) =
  bindNewConstr m tc' tvs (constrType tc' tvs) nc
  where tc' = qualQualify m tc
--bindTy m (ITypeDecl _ r tvs (RecordType fs _)) =
--  flip (foldr (bindRecLabel m r')) fs
--  where r' = qualifyWith m (fromRecordExtId (unqualify r))

bindTy m (IFunctionDecl _ f _ ty) =
  Map.insert (unqualify f)
          (Value (qualQualify m f) (polyType (toQualType m [] ty)))
bindTy _ _ = id

bindConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl
           -> ExpValueEnv -> ExpValueEnv
bindConstr m tc tvs ty0 (ConstrDecl _ evs c tys) =
  bindValue DataConstructor m tc tvs c evs (foldr ArrowType ty0 tys)
bindConstr m tc tvs ty0 (ConOpDecl _ evs ty1 op ty2) =
  bindValue DataConstructor m tc tvs op evs
            (ArrowType ty1 (ArrowType ty2 ty0))

bindNewConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr
              -> NewConstrDecl -> ExpValueEnv -> ExpValueEnv
bindNewConstr m tc tvs ty0 (NewConstrDecl _ evs c ty1) =
  bindValue NewtypeConstructor m tc tvs c evs (ArrowType ty1 ty0)

--bindRecLabel :: ModuleIdent -> QualIdent -> ([Ident],TypeExpr)
--      -> ExpValueEnv -> ExpValueEnv
--bindRecLabel m r ([l],ty) =
--  Map.insert l (Label (qualify l) r (polyType (toQualType m [] ty)))

bindValue :: (QualIdent -> ExistTypeScheme -> ValueInfo) -> ModuleIdent
          -> QualIdent -> [Ident] -> Ident -> [Ident] -> TypeExpr
          -> ExpValueEnv -> ExpValueEnv
bindValue f m tc tvs c evs ty = Map.insert c (f (qualifyLike tc c) sigma)
  where sigma = ForAllExist (length tvs) (length evs) (toQualType m tvs ty)
        qualifyLike x = maybe qualify qualifyWith (qualidMod x)

-- arities
bindA :: ModuleIdent -> IDecl -> ExpArityEnv -> ExpArityEnv
bindA m (IDataDecl _ _ _ cs) expAEnv
   = foldr (bindConstrA m) expAEnv (catMaybes cs)
bindA m (IFunctionDecl _ f a _) expAEnv
   = Map.insert (unqualify f) (ArityInfo (qualQualify m f) a) expAEnv
bindA _ _ expAEnv = expAEnv

bindConstrA :: ModuleIdent -> ConstrDecl -> ExpArityEnv -> ExpArityEnv
bindConstrA m (ConstrDecl _ _ c tys) expAEnv
   = Map.insert c (ArityInfo (qualifyWith m c) (length tys)) expAEnv
bindConstrA m (ConOpDecl _ _ _ c _) expAEnv
   = Map.insert c (ArityInfo (qualifyWith m c) 2) expAEnv

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

expandSpecs :: ModuleIdent -> ExpTCEnv -> ExpValueEnv -> ImportSpec
            -> [Import]
expandSpecs m tcEnv tyEnv (Importing _ is) =
  concatMap (expandImport m tcEnv tyEnv) is
expandSpecs m tcEnv tyEnv (Hiding _ is) =
  concatMap (expandHiding m tcEnv tyEnv) is

expandImport :: ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Import -> [Import]
expandImport m tcEnv tyEnv (Import             x) = expandThing m tcEnv tyEnv x
expandImport m tcEnv _     (ImportTypeWith tc cs) = [expandTypeWith m tcEnv tc cs]
expandImport m tcEnv _     (ImportTypeAll     tc) = [expandTypeAll  m tcEnv tc   ]

expandHiding :: ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Import -> [Import]
expandHiding m tcEnv tyEnv (Import             x) = expandHide m tcEnv tyEnv x
expandHiding m tcEnv _     (ImportTypeWith tc cs) = [expandTypeWith m tcEnv tc cs]
expandHiding m tcEnv _     (ImportTypeAll     tc) = [expandTypeAll  m tcEnv tc   ]

-- try to expand as type constructor
expandThing :: ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Ident -> [Import]
expandThing m tcEnv tyEnv tc = case Map.lookup tc tcEnv of
  Just _  -> expandThing' m tyEnv tc $ Just [ImportTypeWith tc []]
  Nothing -> expandThing' m tyEnv tc Nothing

-- try to expand as function / data constructor
expandThing' :: ModuleIdent -> ExpValueEnv -> Ident -> Maybe [Import] -> [Import]
expandThing' m tyEnv f tcImport = case Map.lookup f tyEnv of
  Just v
    | isConstr v -> fromMaybe (errorAt' $ importDataConstr m f) tcImport
    | otherwise  -> Import f : fromMaybe [] tcImport
  Nothing -> fromMaybe (errorAt' $ undefinedEntity m f) tcImport
  where isConstr (DataConstructor    _ _) = True
        isConstr (NewtypeConstructor _ _) = True
        isConstr (Value              _ _) = False
        isConstr (Label            _ _ _) = False

-- try to hide as type constructor
expandHide :: ModuleIdent -> ExpTCEnv -> ExpValueEnv -> Ident -> [Import]
expandHide m tcEnv tyEnv tc = case Map.lookup tc tcEnv of
  Just _  -> expandHide' m tyEnv tc $ Just [ImportTypeWith tc []]
  Nothing -> expandHide' m tyEnv tc Nothing

-- try to hide as function / data constructor
expandHide' :: ModuleIdent -> ExpValueEnv -> Ident -> Maybe [Import] -> [Import]
expandHide' m tyEnv f tcImport = case Map.lookup f tyEnv of
  Just _  -> Import f : fromMaybe [] tcImport
  Nothing -> fromMaybe (errorAt' $ undefinedEntity m f) tcImport

expandTypeWith ::  ModuleIdent -> ExpTCEnv -> Ident -> [Ident] -> Import
expandTypeWith m tcEnv tc cs = case Map.lookup tc tcEnv of
  Just (DataType _ _ cs') ->
    ImportTypeWith tc (map (checkConstr [c | Just (DataConstr c _ _) <- cs']) cs)
  Just (RenamingType _ _ (DataConstr c _ _)) ->
    ImportTypeWith tc (map (checkConstr [c]) cs)
  Just _  -> errorAt' $ nonDataType tc
  Nothing -> errorAt' $ undefinedEntity m tc
  where
    checkConstr cs' c
      | c `elem` cs' = c
      | otherwise    = errorAt' $ undefinedDataConstr tc c

expandTypeAll :: ModuleIdent -> ExpTCEnv -> Ident -> Import
expandTypeAll m tcEnv tc = case Map.lookup tc tcEnv of
  Just (DataType _ _ cs) ->
    ImportTypeWith tc [c | Just (DataConstr c _ _) <- cs]
  Just (RenamingType _ _ (DataConstr c _ _)) ->
    ImportTypeWith tc [c]
  Just _  -> errorAt' $ nonDataType tc
  Nothing -> errorAt' $ undefinedEntity m tc

-- Auxiliary functions:

addType :: Import -> [Ident] -> [Ident]
addType (Import            _) tcs = tcs
addType (ImportTypeWith tc _) tcs = tc : tcs
addType (ImportTypeAll     _) _   = internalError "Imports.addType"

addValue :: Import -> [Ident] -> [Ident]
addValue (Import            f) fs = f : fs
addValue (ImportTypeWith _ cs) fs = cs ++ fs
addValue (ImportTypeAll     _) _  = internalError "Imports.addType"

addArity :: Import -> [Ident] -> [Ident]
addArity (Import            f) ids = f : ids
addArity (ImportTypeWith _ cs) ids = cs ++ ids
addArity (ImportTypeAll     _) _   = internalError "Imports.addArity"

constrType :: QualIdent -> [Ident] -> TypeExpr
constrType tc tvs = ConstructorType tc $ map VariableType tvs

-- ---------------------------------------------------------------------------

-- After all modules have been imported, the compiler has to ensure that
-- all references to a data type use the same list of constructors.

importUnifyData :: CompilerEnv -> CompilerEnv
importUnifyData cEnv = cEnv { tyConsEnv = importUnifyData' $ tyConsEnv cEnv }

importUnifyData' :: TCEnv -> TCEnv
importUnifyData' tcEnv = fmap (setInfo allTyCons) tcEnv
  where setInfo tcs t   = fromJust $ Map.lookup (origName t) tcs
        allTyCons       = foldr (mergeData . snd) Map.empty $ allImports tcEnv
        mergeData t tcs =
          Map.insert tc (maybe t (fromJust . merge t) $ Map.lookup tc tcs) tcs
          where tc = origName t

-- ---------------------------------------------------------------------------

qualifyLocal :: CompilerEnv -> CompilerEnv -> CompilerEnv
qualifyLocal currentEnv initEnv = currentEnv
  { opPrecEnv = foldr bindQual   pEnv  $ localBindings $ opPrecEnv currentEnv
  , tyConsEnv = foldr bindQual   tcEnv $ localBindings $ tyConsEnv currentEnv
  , valueEnv  = foldr bindGlobal tyEnv $ localBindings $ valueEnv  currentEnv
  , arityEnv  = foldr bindQual   aEnv  $ localBindings $ arityEnv  currentEnv
  }
  where
    pEnv  = opPrecEnv initEnv
    tcEnv = tyConsEnv initEnv
    tyEnv = valueEnv  initEnv
    aEnv  = arityEnv  initEnv
    bindQual (_, y) = qualBindTopEnv "Modules.qualifyEnv" (origName y) y
    bindGlobal (x, y)
      | uniqueId x == 0 = bindQual (x, y)
      | otherwise = bindTopEnv "Modules.qualifyEnv" x y

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
  , arityEnv  = importEntities m True (const True) id mAEnv  $ arityEnv  env
  }
  where mPEnv  = intfEnv bindPrec       i -- all operator precedences
        mTCEnv = intfEnv bindTCHidden   i -- all type constructors
        mTyEnv = intfEnv bindTy         i -- all values
        mAEnv  = intfEnv bindA          i -- all arities


-- Error messages:

undefinedEntity :: ModuleIdent -> Ident -> (Position, String)
undefinedEntity m x = posErr x $
  "Module " ++ moduleName m ++ " does not export " ++ name x

undefinedDataConstr :: Ident -> Ident -> (Position, String)
undefinedDataConstr tc c = posErr c $
  name c ++ " is not a data constructor of type " ++ name tc

nonDataType :: Ident -> (Position, String)
nonDataType tc = posErr tc $
  name tc ++ " is not a data type"

importDataConstr :: ModuleIdent -> Ident -> (Position, String)
importDataConstr _ c = posErr c $
  "Explicit import for data constructor " ++ name c

posErr :: Ident -> String -> (Position, String)
posErr i err = (positionOfIdent i, err)
