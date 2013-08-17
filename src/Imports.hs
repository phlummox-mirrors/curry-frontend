{- |
    Module      :  $Header$
    Description :  Importing interface declarations
    Copyright   :  (c) 2000-2003, Wolfgang Lux
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
                       2013, Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importModules' to bring the imported
    entities into the module's scope, and the function 'qualifyEnv' to
    qualify the environment prior to computing the export interface.
-}
module Imports (importInterfaces, importModules, qualifyEnv) where

import Control.Monad (liftM, unless)
import qualified Control.Monad.State as S (State, gets, modify, runState)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint
import Data.List (nub, (\\))

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax as CS

import Base.CurryTypes (toQualType, toQualTypes, toQualConstrType)
import Base.Messages (Message, posMessage, internalError)
import Base.TopEnv
import Base.Types as BT hiding (isCons)
import Base.TypeSubst (expandAliasType)
import Base.Utils (fromJust') 
import Base.Idents
import Base.Names

import Env.Interface
import Env.ModuleAlias (importAliases, initAliasEnv)
import Env.OpPrec
import Env.TypeConstructor
import Env.Value
import Env.ClassEnv as CE

import Checks.TypeClassesCheck as TCC (buildTypeSchemesNoExpand)

import CompilerEnv
import CompilerOpts

-- |The function 'importModules' brings the declarations of all
-- imported interfaces into scope for the current module.
importModules :: Bool -> Options -> Module -> InterfaceEnv -> (CompilerEnv, [Message])
importModules tcs opts (Module mid _ imps _) iEnv
  = (\ (e, m) -> (expandTCValueEnv opts $ importUnifyData $ insertDummyIdents' e, m))
  $ foldl importModule (initEnv, []) imps
  where
    initEnv = (initCompilerEnv mid)
      { aliasEnv     = importAliases     imps -- import module aliases
      , interfaceEnv = iEnv                   -- imported interfaces
      }
    importModule (env, msgs) (ImportDecl _ m q asM is) =
      case Map.lookup m iEnv of
        Just intf -> let (env', msgs') = importInterface tcs (fromMaybe m asM) q is intf env
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
        Just intf -> importInterfaceIntf initClassEnv intf env
        Nothing   -> internalError $ "Imports.importInterfaces: no interface for "
                                    ++ show m


-- ---------------------------------------------------------------------------
-- Importing an interface into the module
-- ---------------------------------------------------------------------------

-- (At least) five kinds of environments are computed from the interface:
--
-- 1. The operator precedences
-- 2. The type constructors
-- 3. The types of the data constructors and functions (values)
-- 4. The classes in the class environment
-- 5. The instances in the class environments (not using a TopEnv)
--
-- Note that the original names of all entities defined in the imported module
-- are qualified appropriately. The same is true for type expressions.

type IdentMap    = Map.Map Ident
type QIdentMap   = Map.Map QualIdent

type ExpPEnv     = IdentMap PrecInfo
type ExpTCEnv    = IdentMap TypeInfo
type ExpValueEnv = IdentMap ValueInfo
type ExpClassEnv = QIdentMap Class
type ExpClassEnv' = IdentMap Class
type ExpIdentMap = IdentMap QualIdent

-- When an interface is imported, the compiler first transforms the
-- interface into these environments. If an import specification is
-- present, the environments are restricted to only those entities which
-- are included in the specification or not hidden by it, respectively.
-- The resulting environments are then imported into the current module
-- using either a qualified import (if the module is imported qualified)
-- or both a qualified and an unqualified import (non-qualified import).

importInterface :: Bool -> ModuleIdent -> Bool -> Maybe ImportSpec -> Interface
                -> CompilerEnv -> (CompilerEnv, [Message])
importInterface tcs m q is i env = (env'', errs)
  where
  env' = env
    { opPrecEnv = importEntities m q vs id              mPEnv  $ opPrecEnv env
    , tyConsEnv = importEntities m q ts (importData vs) mTCEnv $ tyConsEnv env
    , valueEnv  = importEntities m q vs id              mTyEnv $ valueEnv  env
    , classEnv  = 
      if tcs
      then (classEnv env) {
          theClasses = importEntities' m q cs setPublicMethods mClsEnv' $ 
            theClasses $ classEnv env, 
          theInstances = foldr (importInstance m) (theInstances $ classEnv env) mInstances
        }
      else initClassEnv
    }
  mPEnv  = intfEnv bindPrec i -- all operator precedences
  mTCEnv = intfEnv bindTC   i -- all type constructors
  mTyEnv = intfEnv bindTy   i -- all values
  mClsEnv         = intfEnv (bindCls True)  i -- all classes
  mExportedClsEnv = intfEnv (bindCls False) i -- all exported classes 
                                              -- (i.e., not hidden in the interface)
  mExportedClsEnv' = intfEnv (bindCls' False) i
  (mInstances, depsInstances) = loadInstances i
  -- all imported type constructors / values
  (expandedSpec, errs) = runExpand (expandSpecs is) m mTCEnv mTyEnv mExportedClsEnv'
  ts = isVisible is (Set.fromList $ foldr addType  [] expandedSpec)
  vs = isVisible is (Set.fromList $ foldr addValue [] expandedSpec)
  
  -- class specific importing (considering dependencies!)
  identMap = intfEnv (bindIdentMap False) i
  
  allExportedClasses = Map.keys mExportedClsEnv
  classesInImportSpec = 
    if isImportingAll is
    then allExportedClasses
    -- lookup for each class in the import specification the name under
    -- which it appears in the interface
    else nub $ map lookupQualName $ 
      classesInImportSpec' mExportedClsEnv' expandedSpec
  imported = 
    if isImporting is
    then classesInImportSpec
    -- do not include classes hidden by C(..) or C(funC1, ..., funCn) where
    -- the set {funC1, ..., funCn} contains all publicly exported class methods 
    else allExportedClasses \\ completeClassImports'
  completeClassImports' = nub $ map lookupQualName $  
    completeClassImports mExportedClsEnv' expandedSpec
  hiddenClasses = if isImporting is then [] else classesInImportSpec
  deps = nub $ calcDependencies imported i ++ depsInstances
  
  cs c = if c `elem` imported then True -- import public or hidden
         else if c `elem` deps then True -- import hidden
         else False -- do not import

  -- classes can be imported as hidden or as public
  hflag c = if c `elem` imported && c `notElem` hiddenClasses then False -- import public
            else if c `elem` imported && c `elem` hiddenClasses then True -- import hidden
            else if c `elem` deps then True -- import hidden
            else True -- or False, doesn't matter
  
  mClsEnv' = Map.mapWithKey (setHidden . hflag) mClsEnv
    
  -- |sets the class methods that will be public in the module, 
  -- according to the given import specification
  setPublicMethods :: Class -> Class
  setPublicMethods cls = cls { publicMethods =
    case is of 
      Nothing              -> ms
      Just (Importing _ _) -> fs
      Just (Hiding    _ _) -> ms \\ fs  }
    where
    fs = nub $ getImportedClassMethods (theClass cls) expandedSpec
    ms = publicMethods cls
    
  -- | returns all class methods imported in the import specification via
  -- C(..) or C(f1, ..., fn)  
  getImportedClassMethods :: QualIdent -> [Import] -> [Ident]
  getImportedClassMethods cls = concatMap getImportedClassMethods'
    where
    getImportedClassMethods' :: Import -> [Ident]
    getImportedClassMethods' (ImportTypeWith tc fs) = 
      if tc == unqualify cls then fs else []
    getImportedClassMethods' (Import _) = []
    getImportedClassMethods' (ImportTypeAll _) = 
      internalError "getImportedClassMethods"
      
  -- importing dependencies; always as unqualified!
  env'' = env' 
    { tyConsEnv = importEntities m False ts' id mTCEnv $ tyConsEnv env'
    , valueEnv = importEntities m False ts' id mTyEnv $ valueEnv env'
    }
  
  ts' = (`elem` map unqualify deps)
  
  -- | looks up for the given class from the import specification the name under
  -- which it appears in the interface
  -- TODO: is fromJust here safe?
  lookupQualName :: Ident -> QualIdent
  lookupQualName = fromJust' "Imports" . flip Map.lookup identMap
  
  
      
-- |sets the hidden flag in the given class to true or false
setHidden :: Bool -> Class -> Class
setHidden h c = c { hidden = h } 

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

isImporting :: Maybe ImportSpec -> Bool
isImporting Nothing = True
isImporting (Just (Importing _ _)) = True
isImporting (Just (Hiding    _ _)) = False

isImportingAll :: Maybe ImportSpec -> Bool
isImportingAll Nothing = True
isImportingAll (Just _) = False

importEntities :: Entity a => ModuleIdent -> Bool -> (Ident -> Bool)
               -> (a -> a) -> IdentMap a -> TopEnv a -> TopEnv a
importEntities m q isVisible' f mEnv env =
  foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
        [(x,f y) | (x,y) <- Map.toList mEnv, isVisible' x]
  where importUnqual m' x y = importTopEnv m' x y . qualImportTopEnv m' x y
  
-- |nearly the same as importEntities, only for QualIdents instead of Idents
importEntities' :: Entity a => ModuleIdent -> Bool -> (QualIdent -> Bool)
               -> (a -> a) -> QIdentMap a -> TopEnv a -> TopEnv a
importEntities' m q isVisible' f mEnv env =
  foldr (uncurry (if q then qualImportTopEnv m else importUnqual m)) env
        [(x',f y) | (x,y) <- Map.toList mEnv, let x' = unqualify x, isVisible' x]
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

intfEnv :: (ModuleIdent -> IDecl -> Map.Map m a -> Map.Map m a)
        -> Interface -> Map.Map m a
intfEnv bind (Interface m _ ds) = foldr (bind m) Map.empty ds

-- operator precedences
bindPrec :: ModuleIdent -> IDecl -> ExpPEnv -> ExpPEnv
bindPrec m (IInfixDecl _ fix p op) =
  Map.insert (unqualify op) (PrecInfo (qualQualify m op) (OpPrec fix p))
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
bindTy m (IFunctionDecl _ f a cx ty) env = Map.insert (unqualify f)
  (Value (qualQualify m f) a (polyType ty' `constrainBy` cx') Nothing) env
  where (cx', ty') = toQualConstrType m [] (cx, ty)
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
constrType' m tvs evs ty = ForAllExist BT.emptyContext (length tvs) (length evs)
                                       (toQualType m tvs ty)

bindRecordLabels :: ModuleIdent -> QualIdent -> ([Ident], TypeExpr)
                 -> ExpValueEnv -> ExpValueEnv
bindRecordLabels m r (ls, ty) env = foldr bindLbl env ls
  where
  bindLbl l = Map.insert l (lblInfo l)
  lblInfo l = Label (qualify l) r (polyType $ toQualType m [] ty)

constrType :: QualIdent -> [Ident] -> TypeExpr
constrType tc tvs = ConstructorType tc $ map VariableType tvs

-- | binding classes, either all classes or only exported classes, i.e., 
-- classes not hidden in the interface
bindCls :: Bool -> ModuleIdent -> IDecl -> ExpClassEnv -> ExpClassEnv
bindCls _allClasses m (IClassDecl _ False scx cls tyvar ds defs _deps) env =
  Map.insert cls (mkClass m scx cls tyvar ds defs) env
bindCls allClasses0 m (IClassDecl _ True scx cls tyvar ds defs _deps) env =
  if allClasses0
  then Map.insert cls
                  (mkClass m scx cls tyvar ds defs) env
  else env
bindCls _ _ _ env = env

-- |compute map that maps identifiers to the qualified identifiers under which
-- they appear in the interface
bindIdentMap :: Bool -> ModuleIdent -> IDecl -> ExpIdentMap -> ExpIdentMap
bindIdentMap _allClasses _m (IClassDecl _ False _ cls _ _ _ _) env =
  Map.insert (unqualify cls) cls env
bindIdentMap allClasses0 _m (IClassDecl _ True _ cls _ _ _ _) env =
  if allClasses0
  then Map.insert (unqualify cls) cls env
  else env
bindIdentMap _ _ _ env = env

-- |the same as bindCls', only that it uses a IdentMap instead of a QIdentMap
bindCls' :: Bool -> ModuleIdent -> IDecl -> ExpClassEnv' -> ExpClassEnv'
bindCls' _allClasses m (IClassDecl _ False scx cls tyvar ds defs _deps) env =
  Map.insert (unqualify cls) (mkClass m scx cls tyvar ds defs) env
bindCls' allClasses0 m (IClassDecl _ True scx cls tyvar ds defs _deps) env =
  if allClasses0
  then Map.insert (unqualify cls)
                  (mkClass m scx cls tyvar ds defs) env
  else env
bindCls' _ _ _ env = env

-- |construct a class from an "IClassDecl" or "IHidingClassDecl"
mkClass :: ModuleIdent -> [QualIdent] -> QualIdent -> Ident -> [(Bool, IDecl)] 
        -> [Ident] -> Class
mkClass m scx cls tyvar ds defs = 
  Class { 
    superClasses = map (qualQualify m) scx, 
    theClass = qualQualify m cls, 
    CE.typeVar = tyvar, 
    kind = -1, 
    origMethods = [], 
    methods = map (iFunDeclToMethod m) (map snd ds), 
    typeSchemes = [], 
    defaults = map toDefFun defs,
    hidden = internalError "hidden not yet defined", 
    publicMethods = map (fName . snd) $ filter fst ds }
  where
  toDefFun :: Ident -> Decl 
  toDefFun f = FunctionDecl NoPos Nothing (-1) f 
    -- the implementation of the default method isn't needed
    [Equation NoPos (FunLhs f []) (SimpleRhs NoPos (Tuple (SrcRef []) []) [])]
  fName :: IDecl -> Ident
  fName (IFunctionDecl _ f  _ _ _) = unqualify f
  fName _ = internalError "mkClass in Imports"

-- |convert an IFunctionDecl to the method representation used in "Class"
iFunDeclToMethod :: ModuleIdent -> IDecl -> (Ident, CS.Context, TypeExpr)
iFunDeclToMethod m (IFunctionDecl _ f _a cx te) 
  = (unqualify f, cx, qualifyTypeExpr m te)
iFunDeclToMethod _ _ = internalError "iFunDeclToMethod"

-- |calculates dependecies of the given classes
calcDependencies :: [QualIdent] -> Interface -> [QualIdent]
calcDependencies ids i = 
  concatMap (calcDeps i) ids

-- | calculates the dependencies of one given class (by a simple lookup)
calcDeps :: Interface -> QualIdent -> [QualIdent]
calcDeps i cls =  
  case lookupClassIDecl cls i of
    Just (IClassDecl _ _ _ _ _ _ _ deps) -> deps
    _ -> []

-- |Looks up (if present) an interface class declaration. This is needed
-- for calculating the dependencies of a given class
lookupClassIDecl :: QualIdent -> Interface -> Maybe IDecl
lookupClassIDecl cls (Interface _ _ decls) = list2Maybe $ catMaybes $ map lookupClassIDecl' decls
  where
  lookupClassIDecl' i@(IClassDecl _ _ _ cls' _ _ _ _) | cls == cls' = Just i
  -- lookupClassIDecl' i@(IHidingClassDecl _ _ cls' _ _) | cls == unqualify cls' = Just i
  lookupClassIDecl' _ = Nothing
  list2Maybe [] = Nothing
  list2Maybe [a] = Just a
  list2Maybe (_:_) = internalError "lookupClassIDecl"

-- |returns all imported classes from the given import list
classesInImportSpec' :: ExpClassEnv' -> [Import] -> [Ident]
classesInImportSpec' cEnv = map importId . filter isClassImport
  where
  isClassImport :: Import -> Bool
  isClassImport (Import _) = False
  isClassImport (ImportTypeWith cls _) = isJust $ Map.lookup cls cEnv
  isClassImport (ImportTypeAll _) = internalError "classesInImportSpec"

importId :: Import -> Ident
importId (Import _) = internalError "classesInImportSpec"
importId (ImportTypeWith cls _) = cls
importId (ImportTypeAll _) = internalError "classesInImportSpec"

-- |load instances from interface and return the instances as well as the
-- class dependencies of all instances
loadInstances :: Interface -> ([Instance], [QualIdent])
loadInstances (Interface m _ ds) = foldr (bindInstance m) ([], []) ds

-- |bind an instance into the environment that holds all instances and as well
-- all classes the instances depend on
bindInstance :: ModuleIdent -> IDecl -> ([Instance], [QualIdent]) -> ([Instance], [QualIdent])
bindInstance m (IInstanceDecl _ maybeOrigin scx cls ty tyvars ideps) (is, deps)
  = let inst = Instance {
          context = map (\(qid, id0) -> (qualQualify m qid, id0)) scx, 
          iClass = qualQualify m cls, 
          iType = qualQualify m $ specialTyConToQualIdent ty,
          CE.typeVars = tyvars,
          rules = [], 
          origin = if isNothing maybeOrigin then m else fromJust maybeOrigin
        }
    in (inst:is, deps ++ ideps)
bindInstance _ _ iEnv = iEnv

-- |returns all class imports that are /complete/, i.e., class imports
-- in which all available (i.e., public) class methods are listed
completeClassImports :: ExpClassEnv' -> [Import] -> [Ident]
completeClassImports cEnv = map importId . filter completeClassImport
  where
  completeClassImport :: Import -> Bool
  completeClassImport (Import _) = False
  completeClassImport (ImportTypeWith cls ms) 
    | isJust $ Map.lookup cls cEnv = 
      let c = fromJust $ Map.lookup cls cEnv in 
      Set.fromList ms == Set.fromList (publicMethods c)
    | otherwise = False
  completeClassImport (ImportTypeAll _) = internalError "completelyHiddenClasses"  

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
  , expClassEnv :: ExpClassEnv'
  , errors      :: [Message]
  }

type ExpandM a = S.State ExpandState a

getModuleIdent :: ExpandM ModuleIdent
getModuleIdent = S.gets expModIdent

getTyConsEnv :: ExpandM ExpTCEnv
getTyConsEnv = S.gets expTCEnv

getValueEnv :: ExpandM ExpValueEnv
getValueEnv = S.gets expValueEnv

getClassEnv :: ExpandM ExpClassEnv'
getClassEnv = S.gets expClassEnv

report :: Message -> ExpandM ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

runExpand :: ExpandM a -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> ExpClassEnv' -> (a, [Message])
runExpand expand m tcEnv tyEnv cEnv =
  let (r, s) = S.runState expand (ExpandState m tcEnv tyEnv cEnv [])
  in (r, reverse $ errors s)

expandSpecs :: Maybe ImportSpec -> ExpandM [Import]
expandSpecs Nothing                 = return []
expandSpecs (Just (Importing _ is)) = concat `liftM` mapM expandImport is
expandSpecs (Just (Hiding    _ is)) = concat `liftM` mapM expandHiding is

expandImport :: Import -> ExpandM [Import]
expandImport (Import             x) = expandThing    x
expandImport (ImportTypeWith tc cs) = 
  expandHelper tc (expandClassWith tc cs) (expandTypeWith tc cs) 
expandImport (ImportTypeAll     tc) = 
  expandHelper tc (expandClassAll tc) (expandTypeAll tc)

expandHiding :: Import -> ExpandM [Import]
expandHiding (Import             x) = expandHide x
expandHiding (ImportTypeWith tc cs) = 
  expandHelper tc (expandClassWith tc cs) (expandTypeWith tc cs) 
expandHiding (ImportTypeAll     tc) = 
  expandHelper tc (expandClassAll tc) (expandTypeAll tc)

expandHelper :: Ident -> ExpandM Import -> ExpandM Import -> ExpandM [Import]
expandHelper tc expandClass expandType = do
  cEnv <- getClassEnv
  tyEnv <- getTyConsEnv
  m <- getModuleIdent
  let isClass = tc `Map.member` cEnv
      isCons  = tc `Map.member` tyEnv
  case () of
    () | isClass && isCons     -> report (errAmbiguousEntity m tc) >> return []
       | isClass && not isCons -> (:[]) `liftM` expandClass
       | not isClass && isCons -> (:[]) `liftM` expandType
       | otherwise             -> report (errUndefinedEntity m tc) >> return []

-- try to expand as type constructor or class
expandThing :: Ident -> ExpandM [Import]
expandThing tc = do
  tcEnv <- getTyConsEnv
  cEnv  <- getClassEnv 
  case Map.lookup tc tcEnv of
    Just _  -> expandThing' tc $ Just [ImportTypeWith tc []]
    Nothing -> case Map.lookup tc cEnv of
      Just _ -> expandThing' tc $ Just [ImportTypeWith tc []]
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
  isConstr (Value          _ _ _ _) = False
  isConstr (Label            _ _ _) = False

-- try to hide as type constructor/class
expandHide :: Ident -> ExpandM [Import]
expandHide tc = do
  tcEnv <- getTyConsEnv
  cEnv <- getClassEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandHide' tc $ Just [ImportTypeWith tc []]
    Nothing -> case Map.lookup tc cEnv of
      Just _ -> expandHide' tc $ Just [ImportTypeWith tc []]
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

expandClassWith :: Ident -> [Ident] -> ExpandM Import
expandClassWith cls fs = do
  m <- getModuleIdent
  cEnv <- getClassEnv
  ImportTypeWith cls `liftM` case Map.lookup cls cEnv of
    Nothing -> report (errUndefinedEntity m cls) >> return []
    Just c -> 
      let publicMs = publicMethods c
          invalidFs = nub fs \\ publicMs
      in if null invalidFs
         then return fs
         else report (errUndefinedMethods cls invalidFs) >> return []

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

expandClassAll :: Ident -> ExpandM Import
expandClassAll cls = do
  m <- getModuleIdent
  cEnv <- getClassEnv
  let theClass0 = Map.lookup cls cEnv
  ImportTypeWith cls `liftM` case theClass0 of
    Nothing -> report (errUndefinedEntity m cls) >> return []
    Just c -> return $ publicMethods c

errAmbiguousEntity :: ModuleIdent -> Ident -> Message
errAmbiguousEntity m x = posMessage x $ hsep $ map text
  [ "Ambiguous entity", idName x, "in Module", moduleName m ]

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

errUndefinedMethods :: Ident -> [Ident] -> Message
errUndefinedMethods cls fs = posMessage cls $ 
  text "The following methods are no visible class methods of class" <+> text (show cls)
  <> text ":" <+> brackets (hsep $ punctuate comma (map (text . show) fs))

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
qualifyEnv opts env = expandValueEnv opts
                    $ qualifyLocal env
                    $ foldl (flip (importInterfaceIntf $ classEnv env)) initEnv
                    $ Map.elems
                    $ interfaceEnv env 
  where initEnv = initCompilerEnv $ moduleIdent env

qualifyLocal :: CompilerEnv -> CompilerEnv -> CompilerEnv
qualifyLocal currentEnv initEnv = currentEnv
  { opPrecEnv = foldr bindQual   pEnv  $ localBindings $ opPrecEnv currentEnv
  , tyConsEnv = foldr bindQual   tcEnv $ localBindings $ tyConsEnv currentEnv
  , valueEnv  = foldr bindGlobal tyEnv $ localBindings $ valueEnv  currentEnv
  , classEnv  = (classEnv currentEnv) { theClasses = classesInClassEnv }
  }
  where
    pEnv  = opPrecEnv initEnv
    tcEnv = tyConsEnv initEnv
    tyEnv = valueEnv  initEnv
    cEnv  = classEnv  initEnv
    bindQual   (_, y) = qualBindTopEnv "Imports.qualifyEnv" (origName y) y
    bindGlobal (x, y)
      | idUnique x == 0 = bindQual (x, y)
      | otherwise       = bindTopEnv "Imports.qualifyEnv" x y
    
    classesInClassEnv = 
       foldr bindQual (theClasses cEnv) $ localBindings $ theClasses $ classEnv currentEnv

-- Importing an interface into another interface is somewhat simpler
-- because all entities are imported into the environment. In addition,
-- only a qualified import is necessary. Note that the hidden data types
-- are imported as well because they may be used in type expressions in
-- an interface.

importInterfaceIntf :: ClassEnv -> Interface -> CompilerEnv -> CompilerEnv
importInterfaceIntf cEnv i@(Interface m _ _) env = env
  { opPrecEnv = importEntities m True (const True) id mPEnv  $ opPrecEnv env
  , tyConsEnv = importEntities m True (const True) id mTCEnv $ tyConsEnv env
  , valueEnv  = importEntities m True (const True) id mTyEnv $ valueEnv  env
  , classEnv  = (classEnv env) { 
      theClasses = importEntities' m True (const True) id mClsEnv' $ theClasses $ classEnv env, 
      theInstances = foldr (importInstance m) (theInstances $ classEnv env) mInstances
    }  
  }
  where
  mPEnv  = intfEnv bindPrec     i -- all operator precedences
  mTCEnv = intfEnv bindTCHidden i -- all type constructors
  mTyEnv = intfEnv bindTy       i -- all values
  mClsEnv = intfEnv (bindCls True) i -- all classes
  -- The type schemes might get lost, so we have to recompute them. We
  -- also have to set the hidden flags again, looking them up in the old 
  -- class environment. 
  mClsEnv' = Map.map (buildTypeSchemesNoExpand . setHidden') mClsEnv
  
  canonClassMap' = canonClassMap cEnv
  
  -- we have to set the hidden flags again
  setHidden' :: Class -> Class
  setHidden' cls@(Class { theClass = cName}) = case Map.lookup cName canonClassMap' of
    Nothing -> cls { hidden = False }
    Just c -> cls { hidden = hidden c }

  (mInstances, _deps) = loadInstances i
-- ---------------------------------------------------------------------------
-- Record stuff
-- ---------------------------------------------------------------------------

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
  internalError "Imports.expandRecordTC"
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
  tyEnv'   = fmap (expandRecordTypes tcEnv) $ addImportedLabels m tyEnv
  m        = moduleIdent env

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
    sel = Value (qualRecSelectorId m r l') 1 ty Nothing
    upd = Value (qualRecUpdateId   m r l') 2 ty Nothing
  addLabelType _                       = id

expandRecordTypes :: TCEnv -> ValueInfo -> ValueInfo
expandRecordTypes tcEnv (DataConstructor  qid a (ForAllExist con n m ty)) =
  DataConstructor qid a (ForAllExist con n m (expandRecords tcEnv ty))
expandRecordTypes tcEnv (NewtypeConstructor qid (ForAllExist con n m ty)) =
  NewtypeConstructor qid (ForAllExist con n m (expandRecords tcEnv ty))
expandRecordTypes tcEnv (Value qid a (ForAll con n ty) mc) =
  Value qid a (ForAll con n (expandRecords tcEnv ty)) mc
expandRecordTypes tcEnv (Label qid r (ForAll con n ty)) =
  Label qid r (ForAll con n (expandRecords tcEnv ty))

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

-- ---------------------------------------------------------------------------
-- Dummy identifiers for source code transformations
-- ---------------------------------------------------------------------------

-- When we want to do source code transformations *before* the qualification 
-- transformation, and we have to insert functions from the Prelude/TCPrelude,
-- we have to consider that these functions are still in some stages expanded, 
-- for example in the type checker. 
-- All Prelude/TCPrelude functions that are used in these source code 
-- transformations are qualified with a dummy module, and these functions
-- are imported as if they are contained in this dummy module. 
-- We have to use a dummy module, and not an existing module name, because
-- else we could do an erroneous expansion. Consider for example the following
-- import specifications:
-- 
-- import TCPrelude as P (Eq)
-- import Prelude ()
-- import C as Prelude
-- 
-- Now if we add in a source code transformation "Prelude.&&", and in module
-- C is also an operator "&&" defined, we would after the expansion 
-- of "Prelude.&&" get "C.&&", but that's not the operator we want. 
-- This problem is solved by using a dummy module identifier that contains
-- characters not allowed in a module identifier from the source code, so that
-- it differs from all possible module identifiers. 

-- |Adds the dummy identifiers to the class environment 
insertDummyIdents' :: CompilerEnv -> CompilerEnv
insertDummyIdents' env@(CompilerEnv { valueEnv = v} ) = 
  env { valueEnv = insertDummyIdents v }   

-- |This function adds the needed dummy identifiers to the value environment
insertDummyIdents :: ValueEnv -> ValueEnv
insertDummyIdents vEnv = 
  foldr (\(v, m, v') env -> 
      let dm = if m == preludeMIdent then dummyMIdent else tcDummyMIdent
      in qualImportTopEnv' m (qualifyWith dm v) v' env) vEnv 
  [ (andOp, preludeMIdent, Value (qualifyWith preludeMIdent andOp) 2 
      boolOpTypeScheme Nothing)
  , (orOp,  preludeMIdent, Value (qualifyWith preludeMIdent orOp) 2
      boolOpTypeScheme Nothing)
  , (trueCons', preludeMIdent, 
      DataConstructor (qualifyWith preludeMIdent trueCons') 0 boolConstrTypeScheme)
  , (falseCons', preludeMIdent, 
      DataConstructor (qualifyWith preludeMIdent falseCons') 0 boolConstrTypeScheme)
  , (eqOp, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent eqOp) 2
      (cmpOpTypeScheme eqClsIdent) (Just eqClsIdent))
  , (leqOp, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent leqOp) 2
      (cmpOpTypeScheme ordClsIdent) (Just ordClsIdent))
  , (lessOp, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent lessOp) 2
      (cmpOpTypeScheme ordClsIdent) (Just ordClsIdent))
  -- ((0 -> (1 -> 2)) -> (1 -> (0 -> 2))))
  , (flipIdent, preludeMIdent, Value (qualifyWith preludeMIdent flipIdent) 3
      (ForAll [] 3 (TypeArrow 
        (TypeArrow (tyvar 0) (TypeArrow (tyvar 1) (tyvar 2)))
        (TypeArrow (tyvar 1) (TypeArrow (tyvar 0) (tyvar 2))))) 
      Nothing)
  , (otherwiseIdent, preludeMIdent, Value (qualifyWith preludeMIdent otherwiseIdent)
      0 (ForAll [] 0 preludeBool) Nothing)
  , (errorIdent, preludeMIdent, Value (qualifyWith preludeMIdent errorIdent) 1
      (ForAll [] 1 (TypeArrow preludeString (tyvar 0))) Nothing)
  , (minBoundIdent, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent minBoundIdent)
      0 (ForAll [(boundedClsIdent, tyvar 0)] 1 (tyvar 0)) (Just boundedClsIdent))
  , (maxBoundIdent, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent maxBoundIdent)
      0 (ForAll [(boundedClsIdent, tyvar 0)] 1 (tyvar 0)) (Just boundedClsIdent))
  , (mapIdent, preludeMIdent, Value (qualifyWith preludeMIdent mapIdent) 2
      (ForAll [] 2 (TypeArrow (TypeArrow (tyvar 0) (tyvar 1))
        (TypeArrow (TypeConstructor qListIdP [tyvar 0]) (TypeConstructor qListIdP [tyvar 1]))))
      Nothing)
  , (fromEnumIdent, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent fromEnumIdent)
      1 (ForAll [(enumClsIdent, tyvar 0)] 1 (TypeArrow (tyvar 0) preludeInt)) 
      (Just enumClsIdent))
  , (toEnumIdent, tcPreludeMIdent, Value (qualifyWith tcPreludeMIdent toEnumIdent)
      1 (ForAll [(enumClsIdent, tyvar 0)] 1 (TypeArrow preludeInt (tyvar 0)))
      (Just enumClsIdent))
  , (preludeEnumFromToIdent, preludeMIdent, 
      Value (qualifyWith preludeMIdent preludeEnumFromToIdent) 2 
            (ForAll [] 0 (arrow [preludeInt, preludeInt, TypeConstructor qListIdP [preludeInt]]))
      Nothing)
  , (preludeEnumFromThenToIdent, preludeMIdent, 
      Value (qualifyWith preludeMIdent preludeEnumFromThenToIdent) 3
            (ForAll [] 0 (arrow [preludeInt, preludeInt, preludeInt, TypeConstructor qListIdP [preludeInt]]))
      Nothing)
  ]
                 
  where
  trueCons' = unqualify trueCons
  falseCons' = unqualify falseCons
  preludeBool = TypeConstructor (qualifyWith preludeMIdent $ mkIdent "Bool") []
  preludeChar = TypeConstructor (qualifyWith preludeMIdent $ mkIdent "Char") []
  preludeInt  = TypeConstructor (qualifyWith preludeMIdent $ mkIdent "Int") []
  preludeString = TypeConstructor qListIdP [preludeChar]
  boolOpTypeScheme = 
    (ForAll [] 0 (TypeArrow preludeBool (TypeArrow preludeBool preludeBool)))
  boolConstrTypeScheme = ForAllExist [] 0 0 preludeBool
  cmpOpTypeScheme cls = 
    ForAll [(cls, TypeVariable 0)] 1 
      (TypeArrow (TypeVariable 0) (TypeArrow (TypeVariable 0) preludeBool))
  tyvar i = TypeVariable i
  arrow = foldr1 TypeArrow
