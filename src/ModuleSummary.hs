{- |
    Module      :  $Header$
    Description :  Summarized information of a module
    Copyright   :  (c) 2005, Martin Engelke (men@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Generates a record containing extracted and prepared data from a
    'Curry.Syntax.Module'.
-}
module ModuleSummary (ModuleSummary (..), summarizeModule) where

import Data.Maybe (fromMaybe)

import Curry.Base.Ident
import Curry.Syntax

import Base.Messages (internalError)
import Base.Types

import Env.OpPrec          (mkPrec)
import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)

-- |A record containing data for a module 'm'
data ModuleSummary = ModuleSummary
  { moduleId     :: ModuleIdent   -- ^The name of 'm'
  , interface    :: [IDecl]       -- ^all exported declarations in 'm'
                                  --  (including exported imports)
  , exports      :: [Export]      -- ^The export list extracted from 'm'
  , imports      :: [IImportDecl] -- ^imports
  , infixDecls   :: [IDecl]       -- ^Interfaces of all infix declarations in 'm'
  , typeSynonyms :: [IDecl]       -- ^Interfaces of all type synonyms in 'm'
  } deriving Show


-- |Return a 'ModuleSummary' for a module, its corresponding
-- table of type constructors and its interface
summarizeModule :: TCEnv -> Interface -> Module -> ModuleSummary
summarizeModule tcEnv (Interface iid _ idecls) (Module _ mid mExp imps decls)
  | iid == mid = ModuleSummary
      { moduleId     = mid
      , interface    = idecls
      , exports      = maybe [] (\ (Exporting _ exps) -> exps) mExp
      , imports      = genImports imps
      , infixDecls   = genInfixDecls mid decls
      , typeSynonyms = genTypeSyns tcEnv mid decls
      }
  | otherwise = internalError $
      "Interface " ++ show iid ++ " does not match module " ++ show mid

-- |Generate interface import declarations
genImports :: [ImportDecl] -> [IImportDecl]
genImports = map snd . foldr addImport []
  where
  addImport (ImportDecl pos mid _ _ _) imps = case lookup mid imps of
    Nothing -> (mid, IImportDecl pos mid) : imps
    Just _  -> imps

-- |Generate interface infix declarations in the module
genInfixDecls :: ModuleIdent -> [Decl] -> [IDecl]
genInfixDecls mident decls = concatMap genInfixDecl decls
  where
  genInfixDecl :: Decl -> [IDecl]
  genInfixDecl (InfixDecl pos spec mPrec idents)
    = map (IInfixDecl pos spec (mkPrec mPrec) . qualifyWith mident) idents
  genInfixDecl _ = []

-- ---------------------------------------------------------------------------

-- |Generate interface declarations for all type synonyms in the module.
genTypeSyns :: TCEnv -> ModuleIdent -> [Decl] -> [IDecl]
genTypeSyns tcEnv mident decls
  = concatMap (genTypeSynDecl mident tcEnv) $ filter isTypeSyn decls

isTypeSyn :: Decl -> Bool
isTypeSyn (TypeDecl _ _ _ texpr) = case texpr of
  RecordType _ -> False
  _            -> True
isTypeSyn _ = False

--
genTypeSynDecl :: ModuleIdent -> TCEnv -> Decl -> [IDecl]
genTypeSynDecl mid tcEnv (TypeDecl p i vs ty)
  = [ITypeDecl p (qualifyWith mid i) vs (modifyTypeExpr tcEnv ty)]
genTypeSynDecl _   _     _                    = []

--
modifyTypeExpr :: TCEnv -> TypeExpr -> TypeExpr
modifyTypeExpr tcEnv (ConstructorType q tys) = case qualLookupTC q tcEnv of
  [AliasType _ ar ty] -> modifyTypeExpr tcEnv
                        (genTypeSynDeref (zip [0 .. ar - 1] tys) ty)
  _                   -> ConstructorType (fromMaybe q (lookupTCId q tcEnv))
                                         (map (modifyTypeExpr tcEnv) tys)
modifyTypeExpr _ v@(VariableType _) = v
modifyTypeExpr tcEnv (ArrowType ty1 ty2)
  = ArrowType (modifyTypeExpr tcEnv ty1) (modifyTypeExpr tcEnv ty2)
modifyTypeExpr tcEnv (TupleType tys)
  | null tys  = ConstructorType qUnitId []
  | otherwise = ConstructorType (qTupleId $ length tys)
                                (map (modifyTypeExpr tcEnv) tys)
modifyTypeExpr tcEnv (ListType ty)
  = ConstructorType (qualify listId) [modifyTypeExpr tcEnv ty]
modifyTypeExpr tcEnv (RecordType fields)
  = RecordType (map (\ (lbls, lty) -> (lbls, modifyTypeExpr tcEnv lty)) fields)

--
genTypeSynDeref :: [(Int, TypeExpr)] -> Type -> TypeExpr
genTypeSynDeref its (TypeVariable i) = case lookup i its of
  Nothing -> internalError "ModuleSummary.genTypeSynDeref: unkown type var index"
  Just te -> te
genTypeSynDeref its (TypeConstructor qid tys)
  = ConstructorType qid $ map (genTypeSynDeref its) tys
genTypeSynDeref its (TypeArrow ty1 ty2)
  = ArrowType (genTypeSynDeref its ty1) (genTypeSynDeref its ty2)
genTypeSynDeref its (TypeRecord fields)
  = RecordType
    (map (\ (lab, texpr) -> ([lab], genTypeSynDeref its texpr)) fields)
genTypeSynDeref _ (TypeConstrained _ _) = internalError
  "ModuleSummary.genTypeSynDeref: illegal constrained type occured"
genTypeSynDeref _ (TypeSkolem _) = internalError
  "ModuleSummary.genTypeSynDeref: illegal skolem type occured"

--
lookupTCId :: QualIdent -> TCEnv -> Maybe QualIdent
lookupTCId qident tcEnv = case qualLookupTC qident tcEnv of
  [DataType     qid _ _] -> Just qid
  [RenamingType qid _ _] -> Just qid
  [AliasType    qid _ _] -> Just qid
  _                      -> Nothing
