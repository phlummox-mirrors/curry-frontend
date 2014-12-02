{- |
    Module      :  $Header$
    Description :  Computation of export interface
    Copyright   :  (c) 2000 - 2004, Wolfgang Lux
                       2005       , Martin Engelke
                       2011 - 2013, Björn Peemöller
                       2013       , Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the computation of the exported interface of a
    compiled module. The function 'exportInterface' uses the expanded export
    specifications and the corresponding environments in order to compute
    the interface of the module.
-}
module Exports (exportInterface) where

import           Data.Maybe        (isNothing, catMaybes, isJust, fromJust)
import qualified Data.Set   as Set (delete, fromList, toList)
import Data.List

import Curry.Base.Position
import Curry.Base.Ident
import Curry.Syntax as CS

import Base.CurryTypes (fromQualType, fromQualType', fromContext)
import Base.Messages
import Base.Types as BT
import Base.Names

import Env.OpPrec          (OpPrecEnv, PrecInfo (..), OpPrec (..), qualLookupP)
import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value           (ValueEnv, ValueInfo (..), qualLookupValue)
import Env.ClassEnv as CE

import CompilerEnv

-- ---------------------------------------------------------------------------
-- Computation of the interface
-- ---------------------------------------------------------------------------

-- After checking that the interface is not ambiguous, the compiler
-- generates the interface's declarations from the list of exported
-- functions and values. In order to make the interface more stable
-- against private changes in the module, we remove the hidden data
-- constructors of a data type in the interface when they occur
-- right-most in the declaration. In addition, newtypes whose constructor
-- is not exported are transformed into (abstract) data types.
--
-- If a type is imported from another module, its name is qualified with
-- the name of the module where it is defined. The same applies to an
-- exported function.

-- |The boolean flag indicates whether type class elements should be exported
-- or not 
exportInterface :: CompilerEnv -> Module -> Bool -> Interface
exportInterface env mdl tcs = exportInterface' mdl tcs
  (opPrecEnv env) (tyConsEnv env) (valueEnv env) (classEnv env)

exportInterface' :: Module -> Bool -> OpPrecEnv -> TCEnv -> ValueEnv 
                 -> ClassEnv -> Interface
exportInterface' (Module _ m (Just (Exporting _ es)) _ _) _tcs pEnv tcEnv tyEnv cEnv
  = Interface m imports $ precs ++ hidden0 ++ allDecls
  where
  imports           = map   (IImportDecl NoPos) $ usedModules allDecls
  precs             = foldr (infixDecl m pEnv) [] es
  hidden0           = map   (hiddenTypeDecl m tcEnv) $ hiddenTypes m allDecls
  decls             = foldr (typeDecl m tcEnv cEnv) (foldr (funDecl m tyEnv) [] es) es
  instances         = nub $ map (instanceToIDecl m cEnv) $ 
    concatMap (getClassAndSuperClassInstances cEnv) $ getAllInstances cEnv
  hiddenClasses     = 
    map (classToClassDecl m cEnv True [] {- TODO -}. fromJust . canonLookupClass cEnv) $ 
      nub dependencies \\ nub exportedClasses''
  dependencies      = calculateDependencies cEnv (getAllInstances cEnv) exportedClasses''
  exportedClasses'  = exportedClasses m cEnv es
  exportedClasses'' = map (fromJust . canonClassName m cEnv) exportedClasses'
  allDecls          = 
    nub $ decls ++ dictDecls ++ instances ++ hiddenClasses ++ classElemDecls
  dictionaries      = map Export $ nub $ concatMap (getClassAndSuperClassDicts cEnv) $ 
    getAllInstances cEnv
  dictDecls         = foldr (funDecl m tyEnv) [] dictionaries
  allClasses0       = nub $ exportedClasses'' ++ dependencies
  dictTypes0        = exportsForDictTypes allClasses0
  selFuns           = exportsForSelFuns cEnv allClasses0
  defFuns           = exportsForDefaultFuns cEnv allClasses0
  classElems        = dictTypes0 ++ selFuns ++ defFuns
  classElemDecls    = 
    foldr (typeDecl m tcEnv cEnv) 
          (foldr (funDecl m tyEnv) [] classElems)
          classElems
exportInterface' (Module _ _ Nothing _ _) _ _ _ _ _
  = internalError "Exports.exportInterface: no export specification"

infixDecl :: ModuleIdent -> OpPrecEnv -> Export -> [IDecl] -> [IDecl]
infixDecl m pEnv (Export             f) ds = iInfixDecl m pEnv f ds
infixDecl m pEnv (ExportTypeWith tc cs) ds =
  foldr (iInfixDecl m pEnv . qualifyLike tc) ds cs
infixDecl _ _ _ _ = internalError "Exports.infixDecl: no pattern match"

iInfixDecl :: ModuleIdent -> OpPrecEnv -> QualIdent -> [IDecl] -> [IDecl]
iInfixDecl m pEnv op ds = case qualLookupP op pEnv of
  []                           -> ds
  [PrecInfo _ (OpPrec fix pr)] ->
    IInfixDecl NoPos fix pr (qualUnqualify m op) : ds
  _                            -> internalError "Exports.infixDecl"

typeDecl :: ModuleIdent -> TCEnv -> ClassEnv -> Export -> [IDecl] -> [IDecl]
typeDecl _ _     _    (Export             _) ds = ds
typeDecl m tcEnv cEnv (ExportTypeWith tc cs) ds = case qualLookupTC tc tcEnv of
  [DataType tc' n cs'] ->
    iTypeDecl IDataDecl m tc' n
       (constrDecls m (drop n identSupply) cs cs') : ds
  [RenamingType tc' n (DataConstr c n' [ty])]
    | c `elem` cs ->
        iTypeDecl INewtypeDecl m tc' n (NewConstrDecl NoPos tvs c ty') : ds
    | otherwise -> iTypeDecl IDataDecl m tc' n [] : ds
    where tvs = take n' (drop n identSupply)
          ty' = fromQualType m ty
  [AliasType tc' n ty] -> case ty of
    TypeRecord fs ->
        let ty' = TypeRecord (filter (\ (l,_) -> elem l cs) fs)
        in  iTypeDecl ITypeDecl m tc' n (fromQualType m ty') : ds
    _ -> iTypeDecl ITypeDecl m tc' n (fromQualType m ty) : ds
  [] -> case lookupNonHiddenClasses cEnv tc of
    -- **** TODO ****: export only the listed class methods and hide the others!
    -- We cannot simply drop the hidden class methods, because otherwise 
    -- modules importing the given module would use different dictionaries than
    -- the dictionaries used in the current module where the class is defined. 
    -- The dictionaries must always have the same layout, no matter 
    -- in which module we are. As the layout is determined by the class declaration, 
    -- the whole class declaration must be exported, also the hidden methods 
    -- (for these actually the name doesn't need to be exported, important is only 
    -- the type signature). 
    [c] -> classToClassDecl m cEnv False cs c : ds
    _   -> internalError ("Exports.typeDecl: no class/type: " ++ show tc)
  _ -> internalError "Exports.typeDecl: no type"
typeDecl _ _ _ _ _ = internalError "Exports.typeDecl: no pattern match"

iTypeDecl :: (Position -> QualIdent -> [Ident] -> a -> IDecl)
           -> ModuleIdent -> QualIdent -> Int -> a -> IDecl
iTypeDecl f m tc n = f NoPos (qualUnqualify m tc) (take n identSupply)

constrDecls :: ModuleIdent -> [Ident] -> [Ident] -> [Maybe DataConstr]
            -> [Maybe ConstrDecl]
constrDecls m tvs cs = clean . map (>>= constrDecl m tvs)
  where clean = reverse . dropWhile isNothing . reverse
        constrDecl m' tvs' (DataConstr c n tys)
          | c `elem` cs =
              Just (iConstrDecl (take n tvs') c (map (fromQualType m') tys))
          | otherwise = Nothing

iConstrDecl :: [Ident] -> Ident -> [TypeExpr] -> ConstrDecl
iConstrDecl tvs op [ty1,ty2]
  | isInfixOp op = ConOpDecl NoPos tvs ty1 op ty2
iConstrDecl tvs c tys = ConstrDecl NoPos tvs c tys

funDecl :: ModuleIdent -> ValueEnv -> Export -> [IDecl] -> [IDecl]
funDecl m tyEnv (Export f) ds = case qualLookupValue f tyEnv of
  [Value _ a (ForAll cx _ ty) _] ->
    IFunctionDecl NoPos (qualUnqualify m f) a (fromContext $ unqualifyContext m cx) (fromQualType m ty) : ds
  _ -> internalError $ "Exports.funDecl: " ++ show f
funDecl _ _     (ExportTypeWith _ _) ds = ds
funDecl _ _ _ _ = internalError "Exports.funDecl: no pattern match"

-- |converts a type signature of a class, considering the given class type variable
typeSigToIFunDecl :: ModuleIdent -> Ident -> (Ident, TypeScheme) -> IDecl
typeSigToIFunDecl m tyvar (f, ForAll _cx _ ty) 
  = IFunctionDecl NoPos (qualify f) (arrowArity ty) 
                  -- ignore the context from the type scheme for now 
                  CS.emptyContext (fromQualType' [tyvar] m ty) 

-- |unqualifies an instance
-- unqualInst :: ModuleIdent -> Instance -> Instance
-- unqualInst m (Instance cx cls ty tyvars decls) = 
--   Instance (map unqualifyContextElem cx) (qualUnqualify m cls)
--   (qualUnqualify m ty) tyvars decls
--   where
--   unqualifyContextElem (qid, id0) = (qualUnqualify m qid, id0)

-- |convert an instance to an IInstanceDecl
instanceToIDecl :: ModuleIdent -> ClassEnv -> Instance -> IDecl
instanceToIDecl m cEnv i@(Instance origin' cx cls ty tyvars _) = 
  IInstanceDecl NoPos 
    (if m == origin' then Nothing else Just origin')
    (map unqualifyContextElem cx) (qualUnqualify m cls)
    (toTypeConstructor $ qualUnqualify m ty) tyvars
    (map (qualUnqualify m) (classDeps ++ 
      concatMap (depsForClass cEnv) classDeps ++ dicts)) 
  where
  unqualifyContextElem (qid, id0) = (qualUnqualify m qid, id0)
  classDeps = classesFromInstances cEnv [i]
  -- we depend also on dictionaries for superclasses and the instance type
  dicts = getClassAndSuperClassDicts cEnv i
  
-- |returns all dictionaries for the given instance (i.e., for the instance
-- itself and for superclasses and the instance type)
getClassAndSuperClassDicts :: ClassEnv -> Instance -> [QualIdent]
getClassAndSuperClassDicts cEnv i = map dictNameForInstance insts
  where
  insts = getClassAndSuperClassInstances cEnv i

-- |returns the dictionary name for the given instance
dictNameForInstance :: Instance -> QualIdent
dictNameForInstance (Instance origin' _ cls ty _ _) = 
  qualifyWith origin' $ mkIdent $ mkDictName (show cls) (show ty)


-- |returns the following instances: 
-- * the instance that is passed to the function
-- * the instances for all superclasses and the type of the instance passed to
-- the function
getClassAndSuperClassInstances :: ClassEnv -> Instance -> [Instance]
getClassAndSuperClassInstances cEnv (Instance _ _ cls ty _ _) =
  concat $ zipWith (getInstances cEnv) (cls:scs) (repeat ty) 
  where
  scs = allSuperClasses cEnv cls

-- The compiler determines the list of imported modules from the set of
-- module qualifiers that are used in the interface. Careful readers
-- probably will have noticed that the functions above carefully strip
-- the module prefix from all entities that are defined in the current
-- module. Note that the list of modules returned from
-- 'usedModules' is not necessarily a subset of the modules that
-- were imported into the current module. This will happen when an
-- imported module re-exports entities from another module. E.g., given
-- the three modules
--
-- @
-- module A where { data A = A; }
-- module B(A(..)) where { import A; }
-- module C where { import B; x = A; }
-- @
--
-- the interface for module @C@ will import module @A@ but not module @B@.

usedModules :: [IDecl] -> [ModuleIdent]
usedModules ds = nub' (catMaybes (map qidModule (foldr identsDecl [] ds)))
  where nub' = Set.toList . Set.fromList

identsDecl :: IDecl -> [QualIdent] -> [QualIdent]
identsDecl (IDataDecl       _ tc _ cs) xs =
  tc : foldr identsConstrDecl xs (catMaybes cs)
identsDecl (INewtypeDecl    _ tc _ nc) xs = tc : identsNewConstrDecl nc xs
identsDecl (ITypeDecl       _ tc _ ty) xs = tc : identsType ty xs
identsDecl (IFunctionDecl _ f _ cx ty) xs = f  : identsCx cx (identsType ty xs)
-- TODO: consider also identifiers/classes in the "depends" section of class
-- or instance declarations? 
identsDecl (IClassDecl _ _ scls cls _ sigs _ _) xs = cls : scls ++ foldr identsDecl xs (map snd sigs)
identsDecl (IInstanceDecl _ m scx cls (QualTC ty) _tyvars _) xs = 
  cls : ty : map fst scx ++ qIdentFromModule m ++ xs 
identsDecl (IInstanceDecl _ m scx cls _ _tyvars _) xs = 
  cls : map fst scx ++ qIdentFromModule m ++ xs 
identsDecl _ _ = internalError "Exports.identsDecl: no pattern match"

-- | as we gather qualified identifiers, we have to construct a dummy qualified
-- identifier for the given module name
qIdentFromModule :: Maybe ModuleIdent -> [QualIdent]
qIdentFromModule Nothing  = []
qIdentFromModule (Just m) = [qualifyWith m $ mkIdent "dummy"]

identsConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
identsConstrDecl (ConstrDecl    _ _ _ tys) xs = foldr identsType xs tys
identsConstrDecl (ConOpDecl _ _ ty1 _ ty2) xs =
  identsType ty1 (identsType ty2 xs)

identsNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
identsNewConstrDecl (NewConstrDecl _ _ _ ty) xs = identsType ty xs

identsType :: TypeExpr -> [QualIdent] -> [QualIdent]
identsType (ConstructorType tc tys) xs = tc : foldr identsType xs tys
identsType (VariableType         _) xs = xs
identsType (TupleType          tys) xs = foldr identsType xs tys
identsType (ListType            ty) xs = identsType ty xs
identsType (ArrowType      ty1 ty2) xs = identsType ty1 (identsType ty2 xs)
identsType (RecordType          fs) xs = foldr identsType xs (map snd fs)
identsType s@(SpecialConstructorType _ _) xs = 
  identsType (specialConsToTyExpr s) xs

identsCx :: CS.Context -> [QualIdent] -> [QualIdent]
identsCx (Context cx) xs = foldr identsCxElem xs cx
  where
  identsCxElem :: CS.ContextElem -> [QualIdent] -> [QualIdent]
  identsCxElem (ContextElem cls _var tys) ys = cls : foldr identsType ys tys

-- After the interface declarations have been computed, the compiler
-- eventually must add hidden (data) type declarations to the interface
-- for all those types which were used in the interface but not exported
-- from the current module, so that these type constructors can always be
-- distinguished from type variables.

hiddenTypeDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
hiddenTypeDecl m tcEnv tc = case qualLookupTC (qualQualify m tc) tcEnv of
  [DataType     _ n _] -> hidingDataDecl tc n
  [RenamingType _ n _] -> hidingDataDecl tc n
  -- jrt 2014-10-16: Added for support of record types
  [AliasType    _ n _] -> hidingDataDecl tc n
  _                    -> internalError "Exports.hiddenTypeDecl"
  where hidingDataDecl tc1 n = HidingDataDecl NoPos tc1 $ take n identSupply

hiddenTypes :: ModuleIdent -> [IDecl] -> [QualIdent]
hiddenTypes m ds = [tc | tc <- Set.toList tcs, hidden0 tc]
  where tcs = foldr Set.delete (Set.fromList $ usedTypes ds)
                    (definedTypes ds)
        hidden0 tc = not (isQualified tc) || qidModule tc /= Just m

usedTypes :: [IDecl] -> [QualIdent]
usedTypes ds = foldr usedTypesDecl [] ds

usedTypesDecl :: IDecl -> [QualIdent] -> [QualIdent]
usedTypesDecl (IDataDecl        _ _ _ cs) tcs =
  foldr usedTypesConstrDecl tcs (catMaybes cs)
usedTypesDecl (INewtypeDecl     _ _ _ nc) tcs = usedTypesNewConstrDecl nc tcs
usedTypesDecl (ITypeDecl        _ _ _ ty) tcs = usedTypesType ty tcs
usedTypesDecl (IFunctionDecl _ _ _ cx ty) tcs = usedTypesContext cx (usedTypesType ty tcs)
usedTypesDecl (IClassDecl _ _ _ _ _ sigs _ _) tcs = foldr usedTypesDecl tcs (map snd sigs)
usedTypesDecl (IInstanceDecl _ _ _ _cls (QualTC ty) _ _) tcs = ty : tcs
usedTypesDecl (IInstanceDecl _ _ _ _cls _ _ _) tcs = tcs
usedTypesDecl _                        _   = internalError
  "Exports.usedTypesDecl: no pattern match" -- TODO

usedTypesConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
usedTypesConstrDecl (ConstrDecl    _ _ _ tys) tcs =
  foldr usedTypesType tcs tys
usedTypesConstrDecl (ConOpDecl _ _ ty1 _ ty2) tcs =
  usedTypesType ty1 (usedTypesType ty2 tcs)

usedTypesNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
usedTypesNewConstrDecl (NewConstrDecl _ _ _ ty) tcs = usedTypesType ty tcs

usedTypesType :: TypeExpr -> [QualIdent] -> [QualIdent]
usedTypesType (ConstructorType tc tys) tcs = tc : foldr usedTypesType tcs tys
usedTypesType (VariableType         _) tcs = tcs
usedTypesType (TupleType          tys) tcs = foldr usedTypesType tcs tys
usedTypesType (ListType            ty) tcs = usedTypesType ty tcs
usedTypesType (ArrowType      ty1 ty2) tcs =
  usedTypesType ty1 (usedTypesType ty2 tcs)
usedTypesType (RecordType          fs) tcs = foldr usedTypesType
  tcs (map snd fs)
usedTypesType s@(SpecialConstructorType _ _) tcs = 
  usedTypesType (specialConsToTyExpr s) tcs

usedTypesContext :: CS.Context -> [QualIdent] -> [QualIdent]
usedTypesContext (Context cx) tcs = foldr usedTypesType tcs (concatMap getTy cx)
  where getTy (ContextElem _qid _v ty) = ty

definedTypes :: [IDecl] -> [QualIdent]
definedTypes ds = foldr definedType [] ds
  where
  definedType :: IDecl -> [QualIdent] -> [QualIdent]
  definedType (IDataDecl    _ tc _ _) tcs = tc : tcs
  definedType (INewtypeDecl _ tc _ _) tcs = tc : tcs
  definedType (ITypeDecl    _ tc _ _) tcs = tc : tcs
  definedType _                       tcs = tcs

-- if we have an instance declaration or a class declaration that
-- uses local classes that are *not* exported, we have to provide info
-- for these classes as well, but hidden

-- |returns all classes used directly or indirectly by the given instances
classesFromInstances :: ClassEnv -> [Instance] -> [QualIdent]
classesFromInstances cEnv insts = classesFromClasses True cEnv $ concatMap classesFromInstance insts

-- |returns all classes used directly by the given instance
classesFromInstance :: Instance -> [QualIdent]
classesFromInstance inst = iClass inst : map fst (context inst)

-- |returns all classes used directly or indirectly by the given classes
classesFromClasses :: Bool -> ClassEnv -> [QualIdent] -> [QualIdent]
classesFromClasses includeThisClass cEnv clss = 
  concatMap (classesFromClass includeThisClass cEnv) clss

-- |returns all classes used directly or indirectly by the given class
classesFromClass :: Bool -> ClassEnv -> QualIdent -> [QualIdent]
classesFromClass includeThisClass cEnv cls = 
  (if includeThisClass then (cls:) else id) $ allSuperClasses cEnv cls
 
-- | determines which classes are exported
exportedClasses :: ModuleIdent -> ClassEnv -> [Export] -> [QualIdent]
exportedClasses m cEnv = concatMap exportedClass
  where
  exportedClass (ExportTypeWith qid _) = 
    if isJust $ lookupClass m cEnv qid then [qid] else [] 
  exportedClass (Export             _) = [] 
  exportedClass _                      = internalError "exportedClasses"

-- |calculates the *local* classes on which the given instances and classes
-- depend
-- calcLocalDependencies :: ModuleIdent -> ClassEnv -> [Instance] -> [QualIdent] -> [QualIdent]
-- calcLocalDependencies m cEnv insts = filter (isLocal m) . calculateDependencies cEnv insts 
  
-- |calculates the classes on which the given instances and classes
-- depend
calculateDependencies :: ClassEnv -> [Instance] -> [QualIdent] -> [QualIdent]
calculateDependencies cEnv insts classes = 
  classesFromInstances cEnv insts ++ classesFromClasses False cEnv classes

-- |converts a class into a IClassDecl
classToClassDecl :: ModuleIdent -> ClassEnv -> Bool -> [Ident] -> Class -> IDecl
classToClassDecl m cEnv hidden' fs c =
  IClassDecl NoPos hidden'
       (map (qualUnqualify m) $ superClasses c)
       (qualUnqualify m cName) 
       (CE.typeVar c) 
       (map (\(f, tsc) -> (f `elem` fs, typeSigToIFunDecl m (CE.typeVar c) (f, tsc))) 
            $ typeSchemes c)
       (nub $ concatMap funName $ defaults c)
       (map (qualUnqualify m) (classDeps ++ concatMap 
         (depsForClass cEnv) (cName : classDeps)))
  where
  cName     = theClass c
  classDeps = classesFromClass False cEnv (theClass c)
  
funName :: Decl -> [Ident]
funName (FunctionDecl _ _ _ f _) = [f]
funName _                        = []

-- |calculates all dependencies (dictionary types, selection functions, 
-- default methods) of a given classs
depsForClass :: ClassEnv -> QualIdent -> [QualIdent]
depsForClass cEnv = depsForClass' cEnv . fromJust . canonLookupClass cEnv

depsForClass' :: ClassEnv -> Class -> [QualIdent]
depsForClass' cEnv c = [qualify' $ dictTypeIdent cName]
      ++ map (qualify' . mkIdent) (selFunsNames cEnv cName)
      ++ map qualify' (defaultMethodsIdents cEnv cName)
  where
  cName = theClass c
  qualify' :: Ident -> QualIdent
  qualify' = qualifyLike cName

-- |converts the given class to a hidden class interface declaration
--toHiddenClassDecl :: ModuleIdent -> ClassEnv -> QualIdent -> IDecl
--toHiddenClassDecl m cEnv qid = 
--  IClassDecl NoPos True 
--       (map (qualUnqualify m) $ superClasses c)
--       (qualUnqualify m cName) 
--       (CE.typeVar c) 
--       (map (typeSigToIFunDecl m (CE.typeVar c)) $ typeSchemes c)
--       (nub $ concatMap funName $ defaults c)
--  where
--  cName = theClass c
--  c = fromJust $ canonLookupClass cEnv qid
 
-- for classes, the dictionary types have to be exported, as well as all 
-- selection functions and the default methods

-- |determines the dictionary types for the given classes
exportsForDictTypes :: [QualIdent] -> [Export]
exportsForDictTypes clss = map exportForDictType clss

-- |determines the dictionary type for one given class
exportForDictType :: QualIdent -> Export
exportForDictType cls = 
  ExportTypeWith (qualifyLike cls $ dictTypeIdent cls) []

-- |returns the identifier for the dictionary type of the given class
dictTypeIdent :: QualIdent -> Ident
dictTypeIdent cls = mkIdent $ mkDictTypeName (show cls)

-- |creates export specifications for all selection functions for the given 
-- classes
exportsForSelFuns :: ClassEnv -> [QualIdent] -> [Export]
exportsForSelFuns cEnv clss = concatMap (exportsForSelFuns' cEnv) clss

-- |creates export specifications for all selection functions for a given class
exportsForSelFuns' :: ClassEnv -> QualIdent -> [Export]
exportsForSelFuns' cEnv cls = 
  map (Export . qualifyLike cls . mkIdent) $ selFunsNames cEnv cls
  
-- |returns the names of all dictionary selection functions for the 
-- given class 
selFunsNames :: ClassEnv -> QualIdent -> [String]
selFunsNames cEnv cls = map (mkSelFunName (show cls)) 
    (map show scls ++ map show ms)
  where
  scls   = allSuperClasses cEnv cls
  class0 = fromJust $ canonLookupClass cEnv cls
  ms     = map fst $ typeSchemes class0
  
-- |creates export specifications for all default functions for the given classes
exportsForDefaultFuns :: ClassEnv -> [QualIdent] -> [Export]
exportsForDefaultFuns cEnv clss = concatMap (exportsForDefaultFuns' cEnv) clss 

-- |creates export specifications for all default functions for the given class
exportsForDefaultFuns' :: ClassEnv -> QualIdent -> [Export]
exportsForDefaultFuns' cEnv cls = 
  map (Export . qualifyLike cls) $ defaultMethodsIdents cEnv cls

-- |returns the identifiers of the default methods of a given class
defaultMethodsIdents :: ClassEnv -> QualIdent -> [Ident]
defaultMethodsIdents cEnv cls =
  map  (mkIdent . mkDefFunName (show cls) . show) defaultMethods 
  where
  defaultMethods = concatMap toDef (defaults class0)
  class0 = fromJust $ canonLookupClass cEnv cls
  toDef (FunctionDecl _ _ _ f _) = [f]
  toDef _                        = []
  
