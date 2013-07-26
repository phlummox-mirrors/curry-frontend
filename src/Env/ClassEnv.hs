{- |
    Module      :  $Header$
    Description :  Environment and functionality for type classes
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This file contains the environment definitions for type classes and 
    type classes related functionality. 
-}


module Env.ClassEnv ( 
  -- * class environment
  -- ** the environment data types
  ClassEnv (..), Class (..), Instance (..), initClassEnv
  -- ** various functions for retrieving specific data from the environment 
  , lookupClass, canonLookupClass, canonClassName
  , lookupDefiningClass, lookupMethodTypeScheme, lookupMethodTypeSig
  , allClasses, allLocalClasses, getAllClassMethods, getInstance
  , getAllClassMethodNames, lookupMethodTypeSig', lookupMethodTypeScheme'
  , canonLookupMethodTypeSig', canonLookupMethodTypeScheme'
  , getDefaultMethods, lookupDefiningClass', isClassMethod
  , localInst, importedInst, getAllInstances, getLocalInstances, allInstances
  , lookupNonHiddenClass, allNonHiddenClassBindings, allClassBindings
  , lookupTypeScheme, lookupLocalClass
  , nonHiddenClassEnv
  -- ** functions for modifying the class environment
  , bindClass, bindClassMethods
  -- ** pretty printing
  , ppClass, ppInst
  -- * type classes related functionality 
  , allSuperClasses, isSuperClassOf
  , implies, implies'
  , isValidCx, reduceContext, findPath
  , toHnfs, toHnf, inHnf
  , dictCode, Operation (..), dictType, dictTypes, dictTypeExpr
  ) where

-- import Base.Types hiding ()
import Curry.Base.Ident
import Text.PrettyPrint
import Curry.Syntax.Type
import Curry.Syntax.Utils
import Curry.Syntax.Pretty
import Base.Types hiding (Context, typeVar, typeVars, splitType)
import qualified Base.Types as BT 
import Data.List
import Data.Maybe
import Base.Messages
import Base.Utils
import Control.Monad.State
import Base.Subst (listToSubst)
import Base.Names
import Base.TypeSubst hiding (substContext)
import qualified Data.Map as Map
import Base.TopEnv

-- ----------------------------------------------------------------------------
-- environment definitions
-- ----------------------------------------------------------------------------

-- |The class environment consists of the classes and instances in scope
-- plus a map from class methods to their defining classes
data ClassEnv = ClassEnv 
  -- | environment that maps class identifiers to classes
  { theClasses    :: TopEnv Class
  -- | all instances (with canonical class and type names)
  , theInstances  :: [(Source, Instance)] 
  -- | environment that maps class methods to their corresponding classes
  , classMethods  :: TopEnv Class
  -- | maps canonical (!) class names to the corresponding classes
  , canonClassMap :: Map.Map QualIdent Class
  } 
  deriving Show

data Source = Local | Imported
  deriving Show

data Class = Class
  { superClasses :: [QualIdent]
  , theClass     :: QualIdent -- TODO Ident or QualIdent? 
  , typeVar      :: Ident
  , kind         :: Int
  , methods      :: [(Ident, Context, TypeExpr)]
  , typeSchemes  :: [(Ident, TypeScheme)] 
  , defaults     :: [Decl]
  , hidden       :: Bool 
  , publicMethods:: [Ident] 
  }
  deriving (Eq, Show)

data Instance = Instance
  { context  :: [(QualIdent,Ident)]
  , iClass   :: QualIdent
  , iType    :: QualIdent
  , typeVars :: [Ident]
  , rules    :: [Decl]
  }
  deriving (Eq, Show)
  
initClassEnv :: ClassEnv 
initClassEnv = ClassEnv emptyTopEnv [] emptyTopEnv Map.empty

instance Entity Class where
  origName = theClass
  merge c1 c2 = 
    if theClass c1 == theClass c2
    then Just $ c1 { publicMethods = nub $ publicMethods c1 ++ publicMethods c2 }
    else Nothing

-- ----------------------------------------------------------------------------
-- lookup and data retrieval functions
-- ----------------------------------------------------------------------------

-- |looks up a given, not hidden class from the class environment. Takes as argument
-- the name of the class used in the source code. 
lookupClass :: ClassEnv -> QualIdent -> Maybe Class
lookupClass cEnv c = 
  list2Maybe $ lookupNonHiddenClass cEnv c

lookupLocalClass :: ClassEnv -> QualIdent -> Maybe Class
lookupLocalClass (ClassEnv cEnv _ _ _) c = 
  list2Maybe $ qualLookupLocalTopEnv c (nonHiddenClassEnv cEnv)

-- |looks up a given class from the class environment, returning 
-- a list of matching classes: An empty list means there are no matching
-- classes in scope, a list with more than one element means the class
-- name is ambiguous. Takes as argument the name of the class 
-- used in the source code. 
-- lookupClass' :: ClassEnv -> QualIdent -> [Class]
-- lookupClass' (ClassEnv cEnv _ _ _) c = qualLookupTopEnv c cEnv 

-- |looks up a class if it's not hidden, returning a list of candidates. Takes
-- as argument the name of the class used in the source code. 
lookupNonHiddenClass :: ClassEnv -> QualIdent -> [Class]
lookupNonHiddenClass (ClassEnv cEnv _ _ _) c = 
  qualLookupTopEnv c (nonHiddenClassEnv cEnv)

-- |returns the class environment without hidden classes
nonHiddenClassEnv :: TopEnv Class -> TopEnv Class
nonHiddenClassEnv = filterEnv (not . hidden)

-- |looks up the canonical class name for the given class name that appears
-- in the source code
canonClassName :: ClassEnv -> QualIdent -> Maybe QualIdent
canonClassName cEnv qid = do
  cls <- lookupClass cEnv qid
  return $ theClass cls

-- |looks up a given class in the class environment. The argument must be
-- the canonical class name.
canonLookupClass :: ClassEnv -> QualIdent -> Maybe Class
canonLookupClass cEnv qid = Map.lookup qid (canonClassMap cEnv)

-- |Binds a given class in the class environment. This function is meant
-- to be used for binding classes defined in a source file, not for binding
-- classes imported from elsewhere
bindClass :: ModuleIdent -> TopEnv Class -> Ident -> Class -> TopEnv Class
bindClass m cEnv c cls = 
  qualBindTopEnv "cEnv" qc cls $ bindTopEnv "cEnv" c cls cEnv
  where
  qc = qualifyWith m c
  
-- |returns all classes bound in the class environment. 
allClasses :: TopEnv Class -> [Class]
allClasses = nubBy eqClass . allBoundElems
  where eqClass c1 c2 = theClass c1 == theClass c2
  
-- |returns all locally defined classes bound in the class environment
allLocalClasses :: TopEnv Class -> [Class]
allLocalClasses = nubBy eqClass . map snd . allLocalBindings
  where eqClass c1 c2 = theClass c1 == theClass c2 

-- |looks up the class that defines the given class method
lookupDefiningClass :: ClassEnv -> QualIdent -> Maybe QualIdent
lookupDefiningClass cEnv m = 
  fmap theClass $ lookupDefiningClass' cEnv m 

-- |looks up the class that defines the given class method
lookupDefiningClass' :: ClassEnv -> QualIdent -> Maybe Class
lookupDefiningClass' (ClassEnv _ _ ms _) m = 
  list2Maybe $ qualLookupTopEnv m ms

-- |checks whether the given method is a class method
isClassMethod :: ClassEnv -> QualIdent -> Bool
isClassMethod cEnv = isJust . lookupDefiningClass cEnv

-- |looks up the type scheme of a given class method
lookupMethodTypeScheme :: ClassEnv -> QualIdent -> Maybe TypeScheme
lookupMethodTypeScheme cEnv qid = do
  theClass_ <- lookupDefiningClass' cEnv qid
  let classMethods0 = typeSchemes theClass_
  lookup (unqualify qid) classMethods0  

-- |looks up the method type signature of a given class method
lookupMethodTypeSig :: ClassEnv -> QualIdent -> Maybe (Context, TypeExpr)
lookupMethodTypeSig cEnv qid = do
  theClass_ <- lookupDefiningClass' cEnv qid
  let classMethods0 = methods theClass_
  lookup3 (unqualify qid) classMethods0

lookup3 :: Eq a => a -> [(a, b, c)] -> Maybe (b, c)
lookup3 _ [] =  Nothing
lookup3 x ((a, b, c):ys) | x == a = Just (b, c)
                         | otherwise = lookup3 x ys

-- |get all type signatures of all methods in all classes 
-- in the given class environment; the context of a given method
-- is expanded by the class itself and for the type variable of 
-- the class. 
getAllClassMethods :: ClassEnv -> [(Ident, Context, TypeExpr)]
getAllClassMethods (ClassEnv classes _ _ _) = 
  let msAndCls  = map (\c -> (theClass c, typeVar c, methods c)) (allClasses classes)
      msAndCls' = concatMap (\(tc, tyvar, ms_) -> map (\m -> (tc, tyvar, m)) ms_) msAndCls 
      ms        = map (\(tc, tyvar, (id0, cx, ty)) -> (id0, addClassContext tc tyvar cx, ty)) msAndCls'  
  in ms
  where 
    addClassContext :: QualIdent -> Ident -> Context -> Context
    addClassContext cls tyvar (Context elems) 
      = Context (elems ++ [ContextElem cls tyvar []])  

-- |returns the names of all class methods in all classes in the given class
-- environment
getAllClassMethodNames :: ClassEnv -> [Ident]
getAllClassMethodNames (ClassEnv classes _ _ _) = 
  concatMap (map fst . typeSchemes) (allClasses classes)

-- |binds the class methods in the class methods environment. This function
-- is assumed to be used for classes in the given module, not for imported
-- classes 
bindClassMethods :: ModuleIdent -> [Class] -> TopEnv Class -> TopEnv Class
bindClassMethods m cls env = foldr (bindClassMethods' m) env cls 

-- |binds the methods of one class in the class methods environment 
bindClassMethods' :: ModuleIdent -> Class -> TopEnv Class -> TopEnv Class
bindClassMethods' m cls vEnv = 
  let classMethods0 = map fst $ typeSchemes cls in
  foldr (\id0 env -> 
          qualBindTopEnv "bcm" (qualifyWith m id0) cls $ bindTopEnv "bcm" id0 cls env)
    vEnv
    classMethods0

-- | lookup type signature of class method @f@ in class @cls@, using
-- class names from the source code
lookupMethodTypeSig' :: ClassEnv -> QualIdent -> Ident -> Maybe (Context, TypeExpr)
lookupMethodTypeSig' cEnv cls f = 
  lookupMethodTypeSigHelper cEnv cls f lookupClass

-- |look up type signature of class method @f@ in clas @cls@, using canonical
-- class names
canonLookupMethodTypeSig' :: ClassEnv -> QualIdent -> Ident -> Maybe (Context, TypeExpr)
canonLookupMethodTypeSig' cEnv cls f = 
  lookupMethodTypeSigHelper cEnv cls f canonLookupClass
  
-- |helper function that looks up a method type signature; takes as argument
-- also the lookup function to be used for looking up the given class
lookupMethodTypeSigHelper :: ClassEnv -> QualIdent -> Ident -> 
    (ClassEnv -> QualIdent ->  Maybe Class) -> Maybe (Context, TypeExpr)
lookupMethodTypeSigHelper cEnv cls f lookupFun = do
  theClass_ <- lookupFun cEnv cls
  (_, cx, ty) <- find (\(id0, _, _) -> id0 == f) (methods theClass_)
  return (cx, ty)  

-- |lookup type scheme of class method @f@ in class @cls@, using class names
-- from the source code 
lookupMethodTypeScheme' :: ClassEnv -> QualIdent -> Ident -> Maybe TypeScheme
lookupMethodTypeScheme' cEnv cls f = 
  lookupMethodTypeSchemeHelper cEnv cls f lookupClass

-- |lookup type scheme of class method @f@ in class @cls@, using canonical class names
canonLookupMethodTypeScheme' :: ClassEnv -> QualIdent -> Ident -> Maybe TypeScheme
canonLookupMethodTypeScheme' cEnv cls f =  
  lookupMethodTypeSchemeHelper cEnv cls f canonLookupClass
  
-- |helper function for looking up a type scheme; takes as argument a lookup 
-- function to be used for looking up the class. 
lookupMethodTypeSchemeHelper :: ClassEnv -> QualIdent -> Ident -> 
    (ClassEnv -> QualIdent -> Maybe Class) -> Maybe TypeScheme
lookupMethodTypeSchemeHelper cEnv cls f lookupFun = do
  theClass_ <- lookupFun cEnv cls
  (_, tsc) <- find (\(id0, _) -> id0 == f) (typeSchemes theClass_)
  return tsc

-- |returns the names of the class methods for which a default method is 
-- given 
getDefaultMethods :: Class -> [Ident]
getDefaultMethods cls = map getDefaultMethod (defaults cls)
  where
  getDefaultMethod (FunctionDecl _ _ _ f _) = f
  getDefaultMethod _ = internalError "getDefaultMethods"

-- |returns all locally declared instances
getLocalInstances :: ClassEnv -> [Instance]
getLocalInstances cEnv = map snd $ filter isLocal $ theInstances cEnv
  where isLocal (Local, _) = True
        isLocal _ = False

-- |makes an instance a local instance
localInst :: Instance -> (Source, Instance)
localInst i = (Local, i) 

-- |makes an instance an imported instance
importedInst :: Instance -> (Source, Instance)
importedInst i = (Imported, i)

-- |returns all instances
getAllInstances :: ClassEnv -> [Instance]
getAllInstances cEnv = map snd $ theInstances cEnv

allInstances :: [(Source, Instance)] -> [Instance]
allInstances = map snd 

-- |returns all bindings with classes that are not hidden
allNonHiddenClassBindings :: ClassEnv -> [(QualIdent, Class)]
allNonHiddenClassBindings (ClassEnv cEnv _ _ _) = allBindings $ nonHiddenClassEnv cEnv

-- |returns all bindings
allClassBindings :: ClassEnv -> [(QualIdent, Class)]
allClassBindings (ClassEnv cEnv _ _ _) = allBindings cEnv 

-- |looks up a type scheme in the given class
lookupTypeScheme :: Class -> Ident -> Maybe TypeScheme
lookupTypeScheme cls f = listToMaybe $ map snd $ filter p (typeSchemes cls)
  where
  p (id0, _tsc) = id0 == f

-- ----------------------------------------------------------------------------
-- type classes related functionality
-- ----------------------------------------------------------------------------

-- |returns *all* superclasses of a given class. The given class name must be
-- in canonical form
allSuperClasses :: ClassEnv -> QualIdent -> [QualIdent]
allSuperClasses cEnv c = let
  theClass0 = canonLookupClass cEnv c
  scs = maybe [] superClasses theClass0 in
  nub $ scs ++ concatMap (allSuperClasses cEnv) scs
  
-- |checks whether a given class is a superclass of another class. Both class 
-- names must be in canonical form
isSuperClassOf :: ClassEnv -> QualIdent -> QualIdent -> Bool
isSuperClassOf cEnv c1 c2 = c1 `elem` allSuperClasses cEnv c2

-- |does a specific context imply a given type assertion?
implies :: ClassEnv -> BT.Context -> (QualIdent, Type) -> Bool
implies cEnv cx (qid, ty) = 
  any (\(qid', ty') -> ty == ty' && (qid == qid' || isSuperClassOf cEnv qid qid')) cx
  ||
  (isCons ty && 
    let (xi, tys) = splitType ty
        inst = getInstance cEnv qid xi
        result = fmap (\i -> 
          let cx' = context i
              ids = typeVars i
              s = zip' ids tys
              cx'' = substContext s cx'
          in null (isValidCx cEnv cx'') && implies' cEnv cx cx'') inst
    in maybe False id result)

-- |does a specific context imply another?
implies' :: ClassEnv -> BT.Context -> BT.Context -> Bool
implies' cEnv cx cx' = 
  all (\c' -> implies cEnv cx c') cx' 

-- |get all instances for a given type
-- getInstancesForType :: ClassEnv -> QualIdent -> [Instance]
-- getInstancesForType cEnv qid = filter (\inst -> iType inst == qid) (theInstances cEnv)

-- |helper function
substContext :: [(Ident, Type)] -> [(QualIdent, Ident)] -> BT.Context
substContext subst0 cx = concatMap mfun cx
  where
  mfun (qid, id0) = maybe [] (\id' -> [(qid, id')]) (lookup id0 subst0) 

splitType :: Type -> (QualIdent, [Type])
splitType ty = 
  maybe (internalError "splitType") id (BT.splitType ty)

-- | Performs context reduction. When two contexts are equal except for 
-- the types of the context elements, and it exists an 1:1 mapping for the types, 
-- the resulting reduced contexts are also the same except for renaming using 
-- the mentioned mapping. This is important, because we must rely on the fact
-- that reduced contexts always have the same order of the context elements.
-- 
-- The context reduction preserves also the order of the elements, under
-- the assumption, that all context elements are in HNF. This property
-- is needed, because we want the following: If there is a type signature,
-- the elements in the inferred context should have the same order as 
-- in the type signature. 
-- 
-- This is especially important for the dictionaries: Thus we can
-- assure, that when in the dictionary code creation, a dictionary is
-- constructed out of other dictionaries, these dictionaries are always
-- passed in the correct order, given by the context of the instance
-- declaration, because this context is also copied to the dictionary type
-- signatures.
reduceContext :: ClassEnv -> BT.Context -> BT.Context
reduceContext cEnv cx0 = reduceContext' (toHnfs cEnv cx0)
  where 
  reduceContext' cx = 
    case searchReducible cx of
      Nothing -> cx
      Just cx' -> reduceContext' cx'
  -- search from the back to the front for preserving the order of the context
  -- elements
  searchReducible cx = searchReducible' (length cx - 1) cx
  searchReducible' n cx
    | n == (-1) = Nothing
    | implies cEnv (cx `without` n) (cx !! n) = Just $ cx `without` n
    | otherwise = searchReducible' (n-1) cx

-- |check whether the given constrained type is in head normal form 
inHnf :: (QualIdent, Type) -> Bool
inHnf (_cls, ty) | isCons ty = False
                 | otherwise = True

-- |transform a context by transforming the individual elements into head normal
-- form (where possible)
toHnfs :: ClassEnv -> BT.Context -> BT.Context
toHnfs cEnv cx = concatMap (toHnf cEnv) cx

-- |transform a single context element into head normal form
toHnf :: ClassEnv -> (QualIdent, Type) -> BT.Context
toHnf cEnv (cls, ty) 
  | isCons ty = case inst of
    Nothing -> [(cls, ty)]
    Just i -> let 
      ids = typeVars i
      scon = context i
      mapping = zip' ids tys in
      toHnfs cEnv $ substContext mapping scon
  | otherwise = [(cls, ty)]
  where
  (xi, tys) = splitType ty
  inst = getInstance cEnv cls xi

-- |checks whether the given context is valid. If the context returned is
-- empty, the context is valid. Else the returned context contains the 
-- elements of the context that are not valid
-- TODO: consider superclass relations?
isValidCx :: ClassEnv -> BT.Context -> BT.Context
isValidCx cEnv cx = concatMap isValid' cx
  where
  isValid' :: (QualIdent, Type) -> BT.Context
  isValid' (_cls, TypeVariable _) = []
  isValid' (cls, ty) | isCons ty = 
    let (xi, tys) = splitType ty
        inst = getInstance cEnv cls xi
        tyVars = typeVars (fromJust inst)
        iCx = context (fromJust inst)
        s = zip' tyVars tys in
    if isNothing inst then [(cls, ty)]
    else isValidCx cEnv (substContext s iCx)
  isValid' (_cls, _) = []

-- | returns the instance for a given class and type. Both the class and the 
-- type must be expanded (i.e. Prelude.Eq instead of Eq; Prelude.Bool 
-- instead of Bool)!
getInstance :: ClassEnv -> QualIdent -> QualIdent -> Maybe Instance
getInstance cEnv cls ty = 
  listToMaybe $ filter (\i -> iClass i == cls && iType i == ty) (allInstances $ theInstances cEnv)

-- | finds a path in the class hierarchy from the given class to the given superclass. 
-- The class names passed to this functions must be canonicalized.  
findPath :: ClassEnv -> QualIdent -> QualIdent -> Maybe [QualIdent]
findPath cEnv start target = 
  let paths = findPath' cEnv start target [] in
  if null paths then Nothing 
  else Just $ minimumBy (\l1 l2 -> compare (length l1) (length l2)) paths
    
 
findPath' :: ClassEnv -> QualIdent -> QualIdent -> [QualIdent] -> [[QualIdent]]
findPath' cEnv start target path
  | start == target = [reverse (target:path)]
  | otherwise = concatMap (\sc -> findPath' cEnv sc target (start:path)) 
                          (maybe [] superClasses (canonLookupClass cEnv start))

-- ----------------------------------------------------------------------------
-- dictionary code creation 
-- ----------------------------------------------------------------------------

type Dict = (QualIdent, Type)

-- |the abstract code used for generating dictionaries
data Operation
  = Dictionary Dict            -- ^ a simple dictionary
  | SelSuperClass Dict Dict    -- ^ select from the first dictionary the second
  | BuildDict Dict [Operation] -- ^ build a dictionary with the given operations
  deriving (Eq, Show)
  

-- | this function creates the (abstract) necessary code that is needed for
-- creating a given dictionary from the available dictionaries. 
-- This function is assumed to be called after all type classes checks succeeded, 
-- so the internalError or an error from fromJust should not occur.  
dictCode :: ClassEnv -> BT.Context -> Dict -> Operation
dictCode cEnv available (qid, ty) 
  | any equalCxElem available = Dictionary $ head $ filter equalCxElem available
  | any subClass available = SelSuperClass (head $ filter subClass available) (qid, ty)
  | isCons ty = 
    let (xi, tys) = splitType ty
        -- new version, doesn't work with empty dictionaries: 
        {-dictType0 = dictType cEnv qid
        s = singleSubst 0 ty
        concreteDictType = subst s dictType0
        dictName = mkDictName (show qid) (show xi)
        -- TODO: lookupValue/qualifiedLookupValue?
        [Value _ _ (ForAll infCx _ infDictType)] = 
          lookupValue (mkIdent $ dictName) vEnv
        
        -- alternative 1: use unifyTypes
        {-
        s' = either 
          (internalError 
            ("unifyTypes dictCode concrete vs. inferred:\n" 
              ++ show concreteDictType ++ "\n" ++ show infDictType))
          id $ unifyTypes infDictType concreteDictType
        -}
        
        -- alternative 2: use special buildMapping function
        s' = buildMapping infDictType concreteDictType
        
        cx' = subst s' infCx
        -}
        
        -- old version: 
        
        -- safe under the above assumptions  
        inst = fromJust $ getInstance cEnv qid xi
        ids = typeVars inst
        -- do context reduction of the instance context! As reduceContext
        -- wants Int's as type variables and no Ident's, we have to convert
        -- the present identifiers to numbers and after the context reduction
        -- the numbers back to identifiers again.   
        tyVarsMapping = zip ids [0..]
        origCx = context inst
        cxElem (qid0, id0) = (qid0, TypeVariable $ fromJust $ lookup id0 tyVarsMapping)
        reducedCx = reduceContext cEnv $ map cxElem origCx
        reverseTyVarsMapping = zip [0..] ids
        cxElem' (qid0, TypeVariable n) = (qid0, fromJust $ lookup n reverseTyVarsMapping)
        cxElem' _ = internalError "cxElem'"
        newCx = map cxElem' reducedCx
        
        mapping = zip' ids tys
        cx' = substContext mapping newCx
        
    in 
    BuildDict (qid, ty) (map (dictCode cEnv available) cx')
  | otherwise = internalError ("dictCode: Cannot construct dictionary " 
                               ++ show (qid, ty)++ 
                               " from the following dictionaries:\n" ++ show available) 
 where
 equalCxElem = \(qid', ty') -> qid' == qid && ty' == ty
 subClass = \(qid', ty') -> ty == ty' && isSuperClassOf cEnv qid qid'  

-- ----------------------------------------------------------------------------

-- |This function calculates the dictionary types for all given classes, 
-- using always fresh variables. The passed class identifiers must be canonical.  
dictTypes :: ClassEnv -> [QualIdent] -> [Type]
dictTypes cEnv qids = evalState (mapM (dictType' cEnv) qids) initFreshVar

-- |This function calculates the dictionary type for the given class
dictType :: ClassEnv -> QualIdent -> Type
dictType cEnv cls = evalState (dictType' cEnv cls) initFreshVar

dictType' :: ClassEnv -> QualIdent -> State Int Type
dictType' cEnv cls  = do
  let c = fromJust $ canonLookupClass cEnv cls
      scs = superClasses c
      tschemes = map snd $ typeSchemes c
  -- get the types for all superclasses
  tsScs <- mapM (dictType' cEnv) scs
  -- get the types of the class functions
  funTs <- mapM transTypeScheme tschemes
  -- build the dictionary tuple (or value, if there is only one element)
  return $ case null (tsScs ++ funTs) of
    True -> unitType
    False -> case length (tsScs ++ funTs) == 1 of
      True -> case length tsScs == 1 of
        True -> head tsScs
        False -> head funTs
      False -> tupleType (tsScs ++ funTs)

-- |for each class method, instantiate its type with new type variables, 
-- so that the different types have no common type variables
transTypeScheme :: TypeScheme -> State Int Type
transTypeScheme (ForAll _ _ ty) = do 
  -- instantiate only those type variables that are not refering to the
  -- type variable of the class (here always "0")
  let tvars = (nub $ BT.typeVars ty) \\ [0] 
  freshVars <- replicateM (length tvars) freshTyVar
  let mapping = zip tvars (map TypeVariable freshVars)
      zeroArity = arrowArity ty == 0
      ty' = subst (listToSubst mapping) ty
  return $ if zeroArity then TypeArrow unitType ty' else ty'

freshTyVar :: State Int Int
freshTyVar = do
  n <- get
  put (n+1)
  return n

initFreshVar :: Int
initFreshVar = 1 -- not zero! 

-- ----------------------------------------------------------------------------

-- |returns a type expression representing the type of the dictionary for
-- the given class (here the canonicalized name must be given)
dictTypeExpr :: ClassEnv -> QualIdent -> TypeExpr
dictTypeExpr cEnv cls = 
  case null (scsTypes ++ methodTypes) of
    True -> TupleType [] -- unit
    False -> case length (scsTypes ++ methodTypes) == 1 of
      True -> case length scsTypes == 1 of
        True -> head scsTypes
        False -> head methodTypes
      False -> TupleType (scsTypes ++ methodTypes)
  where
  c = fromJust $ canonLookupClass cEnv cls
  scs = superClasses c
  theMethods = methods c
  
  scsTypes = map (\cls0 -> ConstructorType 
                             (qualify $ mkIdent $ mkDictTypeName $ show cls0) 
                             [VariableType $ typeVar c]) scs
  methodTypes = map considerZeroArity theMethods 
  
  considerZeroArity :: (Ident, Context, TypeExpr) -> TypeExpr
  considerZeroArity (_m, _cx, ty) = if arrowArityTyExpr ty /= 0
    then ty
    else ArrowType (TupleType []) ty  

-- ----------------------------------------------------------------------------
-- Pritty printer functions
-- ----------------------------------------------------------------------------
{-
ppClasses :: ClassEnv -> Doc
ppClasses (ClassEnv classes ifs mmap) = 
  vcat (map (\(qid, cls) -> text (show qid) <> text ":" $+$ nest 4 (ppClass cls)) 
            (allBindings classes)) 
  $$ vcat (map ppInst ifs)
  $$ text (show mmap)
-}  
  
ppClass :: Class -> Doc
ppClass (Class {superClasses = sc, theClass = tc, typeVar = tv, 
                kind = k, methods = ms, defaults = ds, typeSchemes = tscs, 
                hidden = h, publicMethods = pms })
  = (if h then text "hidden" else empty) <+> text "class<" <> text (show k) <> text ">" 
  <+> parens (hsep $ punctuate (text ",") (map (text . show) sc))
  <> text " => " <> text (show tc)
  <+> text (show tv) <+> text "where"
  $$ vcat (map (\(id0, cx, ty) -> 
                 nest 2 (if id0 `elem` pms then text "public" else text "hidden") 
                         <+> ppIdent id0 <+> text "::" <+> ppContext cx <+> ppTypeExpr 0 ty)
               ms)
  $$ vcat (map (\(id0, tsc) -> nest 2 (ppIdent id0 <+> text "::" <+> text (show tsc))) tscs) 
  $$ nest 2 (vcat $ map ppDecl ds)

ppInst :: Instance -> Doc
ppInst (Instance {context = cx, iClass = ic, iType = it, typeVars = tvs, rules = rs})
  = text "instance" 
  <+> parens (hsep $ punctuate (text ",") (map (\(qid, tid) -> text (show qid) <+> text (show tid)) cx))
  <> text " => " <> text (show ic) <+> text "(" <> text (show it)
  <+> hsep (map (text. show) tvs) <> text ")" <+> text "where"
  $$ nest 2 (vcat $ map ppDecl rs)

-- ----------------------------------------------------------------------------
-- Helper functions
-- ----------------------------------------------------------------------------

list2Maybe :: [a] -> Maybe a
list2Maybe [] = Nothing
list2Maybe [x] = Just x
list2Maybe (_:_) = Nothing