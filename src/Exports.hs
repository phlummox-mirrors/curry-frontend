{- |
    Module      :  $Header$
    Description :  Cumputation of export interface
    Copyright   :  (c) 2000 - 2004, Wolfgang Lux
                       2005       , Martin Engelke
                       2011 - 2013, Björn Peemöller
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

import           Data.Maybe      (isNothing, catMaybes)
import qualified Data.Set as Set (delete, fromList, toList)

import Curry.Base.Position
import Curry.Base.Ident
import Curry.Syntax as CS

import Base.CurryTypes (fromQualType, fromQualType', fromContext)
import Base.Messages
import Base.Types as BT

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

exportInterface :: CompilerEnv -> Module -> Interface
exportInterface env mdl = exportInterface' mdl
  (opPrecEnv env) (tyConsEnv env) (valueEnv env) (classEnv env)

exportInterface' :: Module -> OpPrecEnv -> TCEnv -> ValueEnv -> ClassEnv -> Interface
exportInterface' (Module m (Just (Exporting _ es)) _ _) pEnv tcEnv tyEnv cEnv
  = Interface m imports $ precs ++ hidden ++ decls ++ instances
  where
  imports = map   (IImportDecl NoPos) $ usedModules (decls ++ instances)
  precs   = foldr (infixDecl m pEnv) [] es
  hidden  = map   (hiddenTypeDecl m tcEnv) $ hiddenTypes m (decls ++ instances)
  decls   = foldr (typeDecl m tcEnv cEnv) (foldr (funDecl m tyEnv) [] es) es
  instances = map (instanceToIDecl . unqualInst m) $ getLocalInstances cEnv
exportInterface' (Module _ Nothing _ _) _ _ _ _
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
    TypeRecord fs _ ->
        let ty' = TypeRecord (filter (\ (l,_) -> elem l cs) fs) Nothing
        in  iTypeDecl ITypeDecl m tc' n (fromQualType m ty') : ds
    _ -> iTypeDecl ITypeDecl m tc' n (fromQualType m ty) : ds
  [] -> case lookupClass' cEnv tc of
    -- **** TODO ****: export only the listed class methods and hide the others!
    -- We cannot simply drop the hidden class methods, because otherwise 
    -- modules importing the given module would use different dictionaries than
    -- the dictionaries used in the current module where the class is defined. 
    -- The dictionaries must always have the same layout, no matter 
    -- in which module we are. As the layout is determined by the class declaration, 
    -- the whole class declaration must be exported, also the hidden methods 
    -- (for these actually the name doesn't need to be exported, important is only 
    -- the type signature). 
    [c] -> IClassDecl 
             NoPos 
             (map (qualUnqualify m) $ superClasses c)
             (qualUnqualify m $ theClass c) 
             (CE.typeVar c) 
             (map (typeSigToIFunDecl m (CE.typeVar c)) $ typeSchemes c) : ds
    _ -> internalError "Exports.typeDecl: no class"
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
  [Value _ a (ForAll cx _ ty)] ->
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
unqualInst :: ModuleIdent -> Instance -> Instance
unqualInst m (Instance cx cls ty tyvars decls) = 
  Instance (map unqualifyContextElem cx) (qualUnqualify m cls)
  (qualUnqualify m ty) tyvars decls
  where
  unqualifyContextElem (qid, id0) = (qualUnqualify m qid, id0)

-- |convert an instance to an IInstanceDecl
instanceToIDecl :: Instance -> IDecl
instanceToIDecl (Instance cx cls ty tyvars _) = 
  IInstanceDecl NoPos cx cls ty tyvars

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
identsDecl (IDataDecl    _ tc _ cs) xs =
  tc : foldr identsConstrDecl xs (catMaybes cs)
identsDecl (INewtypeDecl _ tc _ nc) xs = tc : identsNewConstrDecl nc xs
identsDecl (ITypeDecl    _ tc _ ty) xs = tc : identsType ty xs
identsDecl (IFunctionDecl _ f _ cx ty) xs = f  : identsCx cx (identsType ty xs)
identsDecl (IClassDecl _ scls cls _ sigs) xs = cls : scls ++ foldr identsDecl xs sigs
identsDecl (IInstanceDecl _ scx cls ty _tyvars) xs = cls : ty : map fst scx ++ xs 
identsDecl _ _ = internalError "Exports.identsDecl: no pattern match"

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
identsType (RecordType      fs rty) xs =
  foldr identsType (maybe xs (\ty -> identsType ty xs) rty) (map snd fs)
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
  _                    -> internalError "Exports.hiddenTypeDecl"
  where hidingDataDecl tc1 n = HidingDataDecl NoPos tc1 $ take n identSupply

hiddenTypes :: ModuleIdent -> [IDecl] -> [QualIdent]
hiddenTypes m ds = [tc | tc <- Set.toList tcs, hidden tc]
  where tcs = foldr Set.delete (Set.fromList $ usedTypes ds)
                    (definedTypes ds)
        hidden tc = not (isQualified tc) || qidModule tc /= Just m

usedTypes :: [IDecl] -> [QualIdent]
usedTypes ds = foldr usedTypesDecl [] ds

usedTypesDecl :: IDecl -> [QualIdent] -> [QualIdent]
usedTypesDecl (IDataDecl     _ _ _ cs) tcs =
  foldr usedTypesConstrDecl tcs (catMaybes cs)
usedTypesDecl (INewtypeDecl  _ _ _ nc) tcs = usedTypesNewConstrDecl nc tcs
usedTypesDecl (ITypeDecl     _ _ _ ty) tcs = usedTypesType ty tcs
usedTypesDecl (IFunctionDecl _ _ _ cx ty) tcs = usedTypesContext cx (usedTypesType ty tcs)
usedTypesDecl (IClassDecl _ _ _ _ sigs) tcs = foldr usedTypesDecl tcs sigs
usedTypesDecl (IInstanceDecl _ _ _cls ty _) tcs = ty : tcs
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
usedTypesType (RecordType      fs rty) tcs = foldr usedTypesType
  (maybe tcs (\ty -> usedTypesType ty tcs) rty) (map snd fs)
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
