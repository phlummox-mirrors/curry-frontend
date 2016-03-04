{- |
    Module      :  $Header$
    Description :  Importing interface declarations
    Copyright   :  (c) 2000 - 2003, Wolfgang Lux
                       2011       , Björn Peemöller
                       2016       , Jan Tikovsky
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importModules' to bring the imported
    entities into the module's scope, and the function 'qualifyEnv' to
    qualify the environment prior to computing the export interface.
-}
module Imports (importInterfaces, importModules, qualifyEnv) where

import           Data.List                  (nubBy)
import qualified Data.Map            as Map
import           Data.Maybe                 (catMaybes, fromMaybe)
import qualified Data.Set            as Set

import Curry.Base.Ident
import Curry.Base.Monad
import Curry.Syntax

import Base.CurryTypes (toQualType, toQualTypes)
import Base.Messages
import Base.TopEnv
import Base.Types

import Env.Interface
import Env.ModuleAlias (importAliases, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value

import CompilerEnv

importModules :: Monad m => Module -> InterfaceEnv -> [ImportDecl]
              -> CYT m CompilerEnv
importModules mdl@(Module _ mid _ _ _) iEnv expImps
  = ok $ foldl importModule initEnv expImps
  where
    initEnv = (initCompilerEnv mid)
      { aliasEnv     = importAliases expImps -- import module aliases
      , interfaceEnv = iEnv                  -- imported interfaces
      , extensions   = knownExtensions mdl
      }
    importModule env (ImportDecl _ m q asM is) =
      case Map.lookup m iEnv of
        Just intf -> importInterface (fromMaybe m asM) q is intf env
        Nothing   -> internalError $ "Imports.importModules: no interface for "
                                    ++ show m

-- |The function 'importInterfaces' brings the declarations of all
-- imported interfaces into scope for the current 'Interface'.
importInterfaces :: Interface -> InterfaceEnv -> CompilerEnv
importInterfaces (Interface m is _) iEnv
  = importUnifyData $ foldl importModule initEnv is
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

-- When an interface is imported, the compiler first transforms the
-- interface into these environments. If an import specification is
-- present, the environments are restricted to only those entities which
-- are included in the specification or not hidden by it, respectively.
-- The resulting environments are then imported into the current module
-- using either a qualified import (if the module is imported qualified)
-- or both a qualified and an unqualified import (non-qualified import).

importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec -> Interface
                -> CompilerEnv -> CompilerEnv
importInterface m q is (Interface mid _ ds) env = env'
  where
  env' = env
    { opPrecEnv = importEntities (precs  mid) m q vs id              ds $ opPrecEnv env
    , tyConsEnv = importEntities (types  mid) m q ts (importData vs) ds $ tyConsEnv env
    , valueEnv  = importEntities (values mid) m q vs id              ds $ valueEnv  env
    }
  ts = isVisible addType  is
  vs = isVisible addValue is

addType :: Import -> [Ident] -> [Ident]
addType (Import            _) tcs = tcs
addType (ImportTypeWith tc _) tcs = tc : tcs
addType (ImportTypeAll     _) _   = internalError "Imports.addType"

addValue :: Import -> [Ident] -> [Ident]
addValue (Import            f) fs = f : fs
addValue (ImportTypeWith _ cs) fs = cs ++ fs
addValue (ImportTypeAll     _) _  = internalError "Imports.addValue"

isVisible :: (Import -> [Ident] -> [Ident]) -> Maybe ImportSpec
          -> Ident -> Bool
isVisible _   Nothing                 = const True
isVisible add (Just (Importing _ xs)) = (`Set.member`    Set.fromList (foldr add [] xs))
isVisible add (Just (Hiding    _ xs)) = (`Set.notMember` Set.fromList (foldr add [] xs))

importEntities :: Entity a => (IDecl -> [a]) -> ModuleIdent -> Bool
               -> (Ident -> Bool) -> (a -> a) -> [IDecl] -> TopEnv a -> TopEnv a
importEntities ents m q isVisible' f ds env =
  foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
        [ (x,f y) | y <- concatMap ents ds
        , let x = unqualify (origName y), isVisible' x
        ]
  where importUnqual m' x y = importTopEnv m' x y . qualImportTopEnv m' x y

importData :: (Ident -> Bool) -> TypeInfo -> TypeInfo
importData isVisible' (DataType tc n cs) =
  DataType tc n (catMaybes $ map (importConstr isVisible') cs)
importData isVisible' (RenamingType tc n nc) =
  maybe (DataType tc n []) (RenamingType tc n) (importConstr isVisible' nc)
importData _ (AliasType tc n ty) = AliasType tc n ty

importConstr :: (Ident -> Bool) -> DataConstr -> Maybe DataConstr
importConstr isVisible' dc
  | isVisible' (constrIdent dc) = Just dc
  | otherwise                   = Nothing

-- ---------------------------------------------------------------------------
-- Building the initial environment
-- ---------------------------------------------------------------------------

-- In a first step, the four export environments are initialized from
-- the interface's declarations.

-- operator precedences
precs :: ModuleIdent -> IDecl -> [PrecInfo]
precs m (IInfixDecl _ fix prec op) = [PrecInfo (qualQualify m op) (OpPrec fix prec)]
precs _ _                          = []

hiddenTypes :: ModuleIdent -> IDecl -> [TypeInfo]
hiddenTypes _ (HidingDataDecl _ tc tvs) = [DataType tc (length tvs) []]
hiddenTypes m d                         = types m d

-- type constructors
types :: ModuleIdent -> IDecl -> [TypeInfo]
types m (IDataDecl _ tc tvs cs _) = [typeCon DataType m tc tvs (map mkData cs)]
  where
   mkData (ConstrDecl _ evs c tys) =
     DataConstr c (length evs) (toQualTypes m tvs tys)
   mkData (ConOpDecl _ evs ty1 c ty2) =
     DataConstr c (length evs) (toQualTypes m tvs [ty1,ty2])
   mkData (RecordDecl _ evs c fs) =
     RecordConstr c (length evs) labels (toQualTypes m tvs tys)
     where
       (labels, tys) = unzip [(l, ty) | FieldDecl _ ls ty <- fs, l <- ls]

types m (INewtypeDecl _ tc tvs nc _) = [typeCon RenamingType m tc tvs (mkData nc)]
  where
   mkData (NewConstrDecl _ evs c ty) =
     DataConstr c (length evs) [toQualType m tvs ty]
   mkData (NewRecordDecl _ evs c (l, ty)) =
     RecordConstr c (length evs) [l] [toQualType m tvs ty]

types m (ITypeDecl _ tc tvs ty) = [typeCon AliasType m tc tvs (toQualType m tvs ty)]
types _ _                       = []

typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> QualIdent -> [Ident] -> a
typeCon f m tc tvs = f (qualQualify m tc) (length tvs)

-- data constructors, record labels, and functions
values :: ModuleIdent -> IDecl -> [ValueInfo]
values m (IDataDecl _ tc tvs cs hs) =
  map (dataConstr m tc' tvs ty')
      (filter ((\con -> con `notElem` hs || isHiddenButNeeded con)
              . constrId) cs) ++
  map (recLabel m tc' tvs ty') (nubBy sameLabel clabels)
  where tc' = qualQualify m tc
        ty' = constrType tc' tvs
        labels   = [ (l, lty) | RecordDecl _ _ _ fs <- cs
                   , FieldDecl _ ls lty <- fs, l <- ls, l `notElem` hs
                   ]
        clabels  = [(l, constr l, ty) | (l, ty) <- labels]
        constr l = [constrId c | c <- cs, l `elem` recordLabels c]
        -- hidden constructors needed for record updates with visible labels
        hiddenCs = [c | (l, _) <- labels, c <- constr l, c `elem` hs]
        isHiddenButNeeded = flip elem hiddenCs
        sameLabel (l1,_,_) (l2,_,_) = l1 == l2
values m (INewtypeDecl _ tc tvs nc hs) =
  map (newConstr m tc' tvs ty') [nc | nconstrId nc `notElem` hs] ++
  case nc of
    NewConstrDecl _ _ _ _        -> []
    NewRecordDecl _ _ c (l, lty) -> [recLabel m tc tvs ty' (l, [c], lty) | l `notElem` hs]
  where tc' = qualQualify m tc
        ty' = constrType tc' tvs
values m (IFunctionDecl _ f a ty) = [Value (qualQualify m f) a (polyType (toQualType m [] ty))]
values _ _                        = []


dataConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> ConstrDecl -> ValueInfo
dataConstr m tc tvs ty0 (ConstrDecl _ evs c tys) =
  DataConstructor (qualifyLike tc c) arity labels $
  constrType' m tvs evs (foldr ArrowType ty0 tys)
  where arity  = length tys
        labels = replicate arity anonId
dataConstr m tc tvs ty0 (ConOpDecl _ evs ty1 op ty2) =
  DataConstructor (qualifyLike tc op) 2 [anonId, anonId] $
  constrType' m tvs evs (ArrowType ty1 (ArrowType ty2 ty0))
dataConstr m tc tvs ty0 (RecordDecl _ evs c fs) =
  DataConstructor (qualifyLike tc c) arity labels $
  constrType' m tvs evs (foldr ArrowType ty0 tys)
  where fields        = [(l, ty) | FieldDecl _ ls ty <- fs, l <- ls]
        (labels, tys) = unzip fields
        arity         = length labels

newConstr :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr -> NewConstrDecl -> ValueInfo
newConstr m tc tvs ty0 (NewConstrDecl _ evs c ty1) =
  NewtypeConstructor (qualifyLike tc c) anonId $
  constrType' m tvs evs (ArrowType ty1 ty0)
newConstr m tc tvs ty0 (NewRecordDecl _ evs c (l, ty1)) =
  NewtypeConstructor (qualifyLike tc c) l $
  constrType' m tvs evs (ArrowType ty1 ty0)

recLabel :: ModuleIdent -> QualIdent -> [Ident] -> TypeExpr
           -> (Ident, [Ident], TypeExpr) -> ValueInfo
recLabel m tc tvs ty0 (l, cs, lty) = Label ql qcs tysc
  where ql   = qualifyLike tc l
        qcs  = map (qualifyLike tc) cs
        tysc = (polyType (toQualType m tvs (ArrowType ty0 lty)))

constrType' :: ModuleIdent -> [Ident] -> [Ident] -> TypeExpr -> ExistTypeScheme
constrType' m tvs evs ty = ForAllExist (length tvs) (length evs)
                                       (toQualType m tvs ty)

constrType :: QualIdent -> [Ident] -> TypeExpr
constrType tc tvs = ConstructorType tc $ map VariableType tvs

-- ---------------------------------------------------------------------------

-- After all modules have been imported, the compiler has to ensure that
-- all references to a data type use the same list of constructors.

importUnifyData :: CompilerEnv -> CompilerEnv
importUnifyData cEnv = cEnv { tyConsEnv = importUnifyData' $ tyConsEnv cEnv }

importUnifyData' :: TCEnv -> TCEnv
importUnifyData' tcEnv = fmap (setInfo allTyCons) tcEnv
  where
  setInfo tcs t   = case Map.lookup (origName t) tcs of
                         Nothing -> error "Imports.importUnifyData'"
                         Just ty -> ty
  allTyCons       = foldr (mergeData . snd) Map.empty $ allImports tcEnv
  mergeData t tcs =
    Map.insert tc (maybe t (sureMerge t) $ Map.lookup tc tcs) tcs
    where tc = origName t
  sureMerge x y = case merge x y of
                       Nothing -> error "Imports.importUnifyData'.sureMerge"
                       Just z  -> z

-- ---------------------------------------------------------------------------

-- |
qualifyEnv :: CompilerEnv -> CompilerEnv
qualifyEnv env = qualifyLocal env
               $ foldl (flip importInterfaceIntf) initEnv
               $ Map.elems
               $ interfaceEnv env
  where initEnv = initCompilerEnv $ moduleIdent env

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
    bindQual   (_, y) = qualBindTopEnv (origName y) y
    bindGlobal (x, y)
      | hasGlobalScope x = bindQual (x, y)
      | otherwise        = bindTopEnv x y

-- Importing an interface into another interface is somewhat simpler
-- because all entities are imported into the environment. In addition,
-- only a qualified import is necessary. Note that the hidden data types
-- are imported as well because they may be used in type expressions in
-- an interface.

importInterfaceIntf :: Interface -> CompilerEnv -> CompilerEnv
importInterfaceIntf (Interface m _ ds) env = env
  { opPrecEnv = importEntitiesIntf m (precs  m) ds $ opPrecEnv env
  , tyConsEnv = importEntitiesIntf m (hiddenTypes  m) ds $ tyConsEnv env
  , valueEnv  = importEntitiesIntf m (values m) ds $ valueEnv  env
  }

importEntitiesIntf :: Entity a => ModuleIdent -> (IDecl -> [a]) -> [IDecl]
                    -> TopEnv a -> TopEnv a
importEntitiesIntf m ents ds env = foldr importEntity env (concatMap ents ds)
  where importEntity x = qualImportTopEnv (fromMaybe m (qidModule (origName x)))
                                          (unqualify (origName x)) x
