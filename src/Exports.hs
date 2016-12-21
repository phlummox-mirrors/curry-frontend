{- |
    Module      :  $Header$
    Description :  Computation of export interface
    Copyright   :  (c) 2000 - 2004, Wolfgang Lux
                       2005       , Martin Engelke
                       2011 - 2016, Björn Peemöller
                       2015       , Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the computation of the exported interface of a
    compiled module. The function 'exportInterface' uses the expanded export
    specifications and the corresponding environments in order to compute
    the interface of the module.
-}
module Exports (exportInterface) where

import           Data.List         (nub)
import           Data.Maybe        (catMaybes)
import qualified Data.Set   as Set (delete, fromList, toList)

import Curry.Base.Position
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryTypes (fromQualType)
import Base.Messages
import Base.Types

import Env.OpPrec          (OpPrecEnv, PrecInfo (..), OpPrec (..), qualLookupP)
import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value           (ValueEnv, ValueInfo (..), qualLookupValue)

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
  (opPrecEnv env) (tyConsEnv env) (valueEnv env)

exportInterface' :: Module -> OpPrecEnv -> TCEnv -> ValueEnv -> Interface
exportInterface' (Module _ m (Just (Exporting _ es)) _ _) pEnv tcEnv tyEnv
  = Interface m imports $ precs ++ hidden ++ decls
  where
  imports = map   (IImportDecl NoPos) $ usedModules decls
  precs   = foldr (infixDecl m pEnv) [] es
  hidden  = map   (hiddenTypeDecl m tcEnv) $ hiddenTypes m decls
  decls   = foldr (typeDecl m tcEnv) (foldr (funDecl m tyEnv) [] es) es
exportInterface' (Module _ _ Nothing _ _) _ _ _
  = internalError "Exports.exportInterface: no export specification"

infixDecl :: ModuleIdent -> OpPrecEnv -> Export -> [IDecl] -> [IDecl]
infixDecl m pEnv (Export             f) ds = iInfixDecl m pEnv f ds
infixDecl m pEnv (ExportTypeWith tc cs) ds =
  foldr (iInfixDecl m pEnv . qualifyLike tc) ds cs
infixDecl _ _ _ _ = internalError "Exports.infixDecl: no pattern match"

iInfixDecl :: ModuleIdent -> OpPrecEnv -> QualIdent -> [IDecl] -> [IDecl]
iInfixDecl m pEnv op ds = case qualLookupP op pEnv of
  []                        -> ds
  [PrecInfo _ (OpPrec f p)] -> IInfixDecl NoPos f p (qualUnqualify m op) : ds
  _                         -> internalError "Exports.infixDecl"

-- Data types and renaming types whose constructors and field labels are
-- not exported are exported as abstract types, i.e., their constructors
-- do not appear in the interface. If only some constructors or field
-- labels of a type are not exported all constructors appear in the
-- interface, but a pragma marks the constructors and field labels which
-- are not exported as hidden to prevent their use in user code.

typeDecl :: ModuleIdent -> TCEnv -> Export -> [IDecl] -> [IDecl]
typeDecl _ _     (Export             _) ds = ds
typeDecl m tcEnv (ExportTypeWith tc xs) ds = case qualLookupTC tc tcEnv of
  [DataType tc' n cs]
    | null xs   -> iTypeDecl IDataDecl m tc' n []  [] : ds
    | otherwise -> iTypeDecl IDataDecl m tc' n cs' hs : ds
    where hs    = filter (`notElem` xs) (csIds ++ ls)
          cs'   = map (constrDecl m (drop n identSupply)) cs
          ls    = nub (concatMap recordLabels cs')
          csIds = map constrIdent cs
  [RenamingType tc' n c]
    | null xs   -> iTypeDecl IDataDecl    m tc' n [] [] : ds
    | otherwise -> iTypeDecl INewtypeDecl m tc' n nc hs : ds
    where hs  = filter (`notElem` xs) (cId : ls)
          nc  = newConstrDecl m (drop n identSupply) c
          ls  = nrecordLabels nc
          cId = constrIdent c
  [AliasType tc' n ty] -> ITypeDecl NoPos tc'' tvs ty' : ds
    where tc'' = qualUnqualify m tc'
          tvs  = take n identSupply
          ty'  = fromQualType m ty
  _ -> internalError "Exports.typeDecl"
typeDecl _ _ _ _ = internalError "Exports.typeDecl: no pattern match"

iTypeDecl :: (Position -> QualIdent -> [Ident] -> a -> [Ident] -> IDecl)
           -> ModuleIdent -> QualIdent -> Int -> a -> [Ident] -> IDecl
iTypeDecl f m tc n x hs = f NoPos (qualUnqualify m tc) (take n identSupply) x hs

constrDecl :: ModuleIdent -> [Ident] -> DataConstr -> ConstrDecl
constrDecl m tvs (DataConstr c n [ty1,ty2])
  | isInfixOp c
  = ConOpDecl NoPos (take n tvs) (fromQualType m ty1) c (fromQualType m ty2)
constrDecl m tvs (DataConstr   c n     tys)
  = ConstrDecl NoPos (take n tvs) c (map (fromQualType m) tys)
constrDecl m tvs (RecordConstr c n ls  tys)
  = RecordDecl NoPos (take n tvs) c
  $ zipWith (FieldDecl NoPos . return) ls (map (fromQualType m) tys)

newConstrDecl :: ModuleIdent -> [Ident] -> DataConstr -> NewConstrDecl
newConstrDecl m tvs (DataConstr   c n    tys)
  = NewConstrDecl NoPos (take n tvs) c (fromQualType m (head tys))
newConstrDecl m tvs (RecordConstr c n ls tys)
  = NewRecordDecl NoPos (take n tvs) c (head ls, fromQualType m (head tys))

funDecl :: ModuleIdent -> ValueEnv -> Export -> [IDecl] -> [IDecl]
funDecl m tyEnv (Export           f) ds = case qualLookupValue f tyEnv of
  [Value _ a (ForAll _ ty)] ->
    IFunctionDecl NoPos (qualUnqualify m f) a (fromQualType m ty) : ds
  _ -> internalError $ "Exports.funDecl: " ++ show f
funDecl _ _     (ExportTypeWith _ _) ds = ds
funDecl _ _ _ _ = internalError "Exports.funDecl: no pattern match"

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
usedModules ds = nub' (catMaybes (map qidModule (foldr idsDecl [] ds)))
  where nub' = Set.toList . Set.fromList

idsDecl :: IDecl -> [QualIdent] -> [QualIdent]
idsDecl (IDataDecl    _ tc _ cs _) xs = tc : foldr idsConstrDecl xs cs
idsDecl (INewtypeDecl _ tc _ nc _) xs = tc : identsNewConstrDecl nc xs
idsDecl (ITypeDecl      _ tc _ ty) xs = tc : idsType ty xs
idsDecl (IFunctionDecl   _ f _ ty) xs = f  : idsType ty xs
idsDecl _ _ = internalError "Exports.idsDecl: no pattern match"

idsConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
idsConstrDecl (ConstrDecl    _ _ _ tys) xs = foldr idsType xs tys
idsConstrDecl (ConOpDecl _ _ ty1 _ ty2) xs = idsType ty1 (idsType ty2 xs)
idsConstrDecl (RecordDecl     _ _ _ fs) xs = foldr identsFieldDecl xs fs

identsFieldDecl :: FieldDecl -> [QualIdent] -> [QualIdent]
identsFieldDecl (FieldDecl _ _ ty) xs = idsType ty xs

identsNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
identsNewConstrDecl (NewConstrDecl _ _ _     ty) xs = idsType ty xs
identsNewConstrDecl (NewRecordDecl _ _ _ (_,ty)) xs = idsType ty xs

idsType :: TypeExpr -> [QualIdent] -> [QualIdent]
idsType (ConstructorType tc tys) xs = tc : foldr idsType xs tys
idsType (VariableType         _) xs = xs
idsType (TupleType          tys) xs = foldr idsType xs tys
idsType (ListType            ty) xs = idsType ty xs
idsType (ArrowType      ty1 ty2) xs = idsType ty1 (idsType ty2 xs)
idsType (ParenType           ty) xs = idsType ty xs

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
  where
  tcs       = foldr Set.delete (Set.fromList $ usedTypes ds) (definedTypes ds)
  hidden tc = not (isQualified tc) || qidModule tc /= Just m

usedTypes :: [IDecl] -> [QualIdent]
usedTypes ds = foldr utDecl [] ds

utDecl :: IDecl -> [QualIdent] -> [QualIdent]
utDecl (IDataDecl     _ _ _ cs _) tcs = foldr utConstrDecl tcs cs
utDecl (INewtypeDecl  _ _ _ nc _) tcs = utNewConstrDecl nc tcs
utDecl (ITypeDecl     _ _ _ ty  ) tcs = utType ty tcs
utDecl (IFunctionDecl _ _ _ ty  ) tcs = utType ty tcs
utDecl d                          _   = internalError
                                      $ "Exports.utDecl: " ++ show d

utConstrDecl :: ConstrDecl -> [QualIdent] -> [QualIdent]
utConstrDecl (ConstrDecl    _ _ _ tys) tcs = foldr utType tcs tys
utConstrDecl (ConOpDecl _ _ ty1 _ ty2) tcs = utType ty1 (utType ty2 tcs)
utConstrDecl (RecordDecl     _ _ _ fs) tcs = foldr utFieldDecl tcs fs

utFieldDecl :: FieldDecl -> [QualIdent] -> [QualIdent]
utFieldDecl (FieldDecl _ _ ty) tcs = utType ty tcs

utNewConstrDecl :: NewConstrDecl -> [QualIdent] -> [QualIdent]
utNewConstrDecl (NewConstrDecl     _ _ _ ty) tcs = utType ty tcs
utNewConstrDecl (NewRecordDecl _ _ _ (_,ty)) tcs = utType ty tcs

utType :: TypeExpr -> [QualIdent] -> [QualIdent]
utType (ConstructorType tc tys) tcs = tc : foldr utType tcs tys
utType (VariableType         _) tcs = tcs
utType (TupleType          tys) tcs = foldr utType tcs tys
utType (ListType            ty) tcs = utType ty tcs
utType (ArrowType      ty1 ty2) tcs = utType ty1 (utType ty2 tcs)
utType (ParenType           ty) tcs = utType ty tcs

definedTypes :: [IDecl] -> [QualIdent]
definedTypes ds = foldr definedType [] ds
  where
  definedType :: IDecl -> [QualIdent] -> [QualIdent]
  definedType (IDataDecl    _ tc _ _ _) tcs = tc : tcs
  definedType (INewtypeDecl _ tc _ _ _) tcs = tc : tcs
  definedType (ITypeDecl    _ tc _ _  ) tcs = tc : tcs
  definedType _                         tcs = tcs
