{- |
    Module      :  $Header$
    Description :  Transformation of explicit type signatures
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This transformation removes the context in all explicit type signatures 
    by inserting the appropriate dictionary types for each element of the 
    (reduced) context. This is needed for the second type check that expects a
    program without any type class elements. 
    Note that instead of the contexts given in the source code, the reduced
    contexts are used for inserting dictionary type parameters. 
    In the new type signatures, all type synonyms are expanded and all 
    data constructors qualified (because we take the type signature from
    the value environment where this is the case). Because of this, in the
    second run of the type checker, type expansion and constructor qualifying
    must be disabled for type signatures. 
-}


module Transformations.TypeSigs (transformTypeSigs) where

import Data.Maybe

import Curry.Syntax.Type as CS
import Env.ClassEnv
import CompilerEnv
import Env.Value
import Base.Types
import Base.TypeSubst
import Base.Messages
import Curry.Base.Ident
import Base.TopEnv

-- | transforms all type signatures (in explicit type signatures declarations
-- *and* in explicitely typed expressions (!)) by removing their contexts
-- and inserting types for the dictionaries.  
transformTypeSigs :: CompilerEnv -> Module -> Module
transformTypeSigs cEnv (Module c m e i ds) = Module c m e i (concatMap (tsDecl cEnv) ds)

tsDecl :: CompilerEnv -> Decl -> [Decl]
tsDecl _cEnv d@(InfixDecl               _ _ _ _) = [d]
tsDecl _cEnv d@(DataDecl              _ _ _ _ _) = [d]
tsDecl _cEnv d@(NewtypeDecl           _ _ _ _ _) = [d]
tsDecl _cEnv d@(TypeDecl                _ _ _ _) = [d]
tsDecl  cEnv   (TypeSig p _ ids (Context cx) ty) = 
  -- if null cx then [d] else [] 
  map (tsTySig cEnv) splitTySigs
  where
  splitTySigs :: [Decl]
  splitTySigs = map (\id0 -> TypeSig p True [id0] (Context cx) ty) ids  
tsDecl  cEnv   (FunctionDecl p cty id0 i eqs) = [FunctionDecl p cty id0 i (map (tsEqu cEnv) eqs)]
tsDecl _cEnv d@(ForeignDecl        _ _ _ _ _) = [d]
tsDecl _cEnv d@(ExternalDecl             _ _) = [d]
tsDecl  cEnv   (PatternDecl p cty id0 pt rhs) = [PatternDecl p cty id0 pt (tsRhs cEnv rhs)]
tsDecl _cEnv d@(FreeDecl                 _ _) = [d]
tsDecl _cEnv d@(ClassDecl          _ _ _ _ _) = [d]
tsDecl _cEnv d@(InstanceDecl     _ _ _ _ _ _) = [d]

-- | replaces a type signature with the type signature extracted from the 
-- value environment and inserts further dictionary types
tsTySig :: CompilerEnv -> Decl -> Decl
tsTySig cEnv (TypeSig p _ [id0] (Context _cx) _ty) =
  TypeSig p True [id0] (Context []) (fromType newTySig)
  where
  Value _ _ (ForAll cx _ ty) _ = lookupValue' (moduleIdent cEnv) id0 (valueEnv cEnv)

  dictTys = dictTypes (classEnv cEnv) (map fst cx)
  
  -- As the context elements are reduced to HNF (head normal form) 
  -- fromTypeVar shouldn't fail. 
  fromTypeVar :: Type -> Int
  fromTypeVar (TypeVariable i) = i
  fromTypeVar _ = internalError "fromTypeVar"
  
  vars = map (fromTypeVar . snd) cx
  -- Replace the class variable (always 0 in dictTys) 
  -- with the variable given in the context.
  -- TODO: Rename all other variables so that they don't overlap with other type
  -- variables in the type signature AND/OR match the type variables from
  -- the dictionary type with type variables from the type signature.
  -- As currently, no other type variables than the type variable of the class
  -- itself are allowed, this TODO is not yet necessary.
  dictTys' = zipWith (\v ty0 -> subst (singleSubst 0 (TypeVariable v)) ty0) vars dictTys
  
  
  constrNewTySig [] sig = sig
  constrNewTySig (d:ds) sig = constrNewTySig ds (TypeArrow d sig)
  
  newTySig = constrNewTySig (reverse dictTys') ty
tsTySig _ _ = internalError "tsTySig"  

tsEqu :: CompilerEnv -> Equation -> Equation
tsEqu cEnv (Equation p lhs rhs) = Equation p lhs (tsRhs cEnv rhs)

tsRhs :: CompilerEnv -> Rhs -> Rhs
tsRhs cEnv (SimpleRhs p e ds) = SimpleRhs p (tsExpr cEnv e) (concatMap (tsDecl cEnv) ds)
tsRhs cEnv (GuardedRhs cs ds) = GuardedRhs (map (tsCondExpr cEnv) cs) (concatMap (tsDecl cEnv) ds)

tsCondExpr :: CompilerEnv -> CondExpr -> CondExpr
tsCondExpr cEnv (CondExpr p e1 e2) = CondExpr p (tsExpr cEnv e1) (tsExpr cEnv e2)

tsExpr :: CompilerEnv -> Expression -> Expression
tsExpr _cEnv e@(Literal        _) = e
tsExpr _cEnv e@(Variable     _ _) = e
tsExpr _cEnv e@(Constructor    _) = e
tsExpr cEnv    (Paren          e) = tsExpr cEnv e
-- Handle type signature in typed expression by simply removing the context
-- (no dictionaries have to be inserted here, so the context can be ignored)
tsExpr cEnv (Typed   cty e _cx t) = Typed cty (tsExpr cEnv e) CS.emptyContext t
tsExpr cEnv (Tuple       sref es) = Tuple sref (map (tsExpr cEnv) es)
tsExpr cEnv (List        sref es) = List sref (map (tsExpr cEnv) es)
tsExpr cEnv (ListCompr sref e ss) = ListCompr sref (tsExpr cEnv e) (map (tsStmt cEnv) ss)
tsExpr cEnv (EnumFrom     cty e1) = EnumFrom cty (tsExpr cEnv e1)
tsExpr cEnv (EnumFromThen cty e1 e2) = EnumFromThen cty (tsExpr cEnv e1) (tsExpr cEnv e2)
tsExpr cEnv (EnumFromTo   cty e1 e2) = EnumFromTo cty (tsExpr cEnv e1) (tsExpr cEnv e2)
tsExpr cEnv (EnumFromThenTo cty e1 e2 e3) = EnumFromThenTo cty (tsExpr cEnv e1) (tsExpr cEnv e2) (tsExpr cEnv e3)
tsExpr cEnv (UnaryMinus  cty i e) = UnaryMinus cty i (tsExpr cEnv e)
tsExpr cEnv (Apply         e1 e2) = Apply (tsExpr cEnv e1) (tsExpr cEnv e2)
tsExpr cEnv (InfixApply e1 op e2) = InfixApply (tsExpr cEnv e1) op (tsExpr cEnv e2)
tsExpr cEnv (LeftSection    e op) = LeftSection (tsExpr cEnv e) op
tsExpr cEnv (RightSection   op e) = RightSection op (tsExpr cEnv e)
tsExpr cEnv (Lambda    sref ps e) = Lambda sref ps (tsExpr cEnv e)
tsExpr cEnv (Let            ds e) = Let (concatMap (tsDecl cEnv) ds) (tsExpr cEnv e)
tsExpr cEnv (Do             ss e) = Do (map (tsStmt cEnv) ss) (tsExpr cEnv e)
tsExpr cEnv (IfThenElse sref e1 e2 e3) = 
  IfThenElse sref (tsExpr cEnv e1) (tsExpr cEnv e2) (tsExpr cEnv e3)
tsExpr cEnv (Case sref ct e alts) = Case sref ct (tsExpr cEnv e) (map (tsAlt cEnv) alts)
tsExpr cEnv (RecordConstr     fs) = RecordConstr (map (tsField cEnv) fs)
tsExpr cEnv (RecordSelection e i) = RecordSelection (tsExpr cEnv e) i
tsExpr cEnv (RecordUpdate   fs e) = RecordUpdate (map (tsField cEnv) fs) (tsExpr cEnv e)


tsStmt :: CompilerEnv -> Statement -> Statement
tsStmt cEnv (StmtExpr   sref e) = StmtExpr sref (tsExpr cEnv e)
tsStmt cEnv (StmtDecl       ds) = StmtDecl (concatMap (tsDecl cEnv) ds)
tsStmt cEnv (StmtBind sref p e) = StmtBind sref p (tsExpr cEnv e)

tsAlt :: CompilerEnv -> Alt -> Alt
tsAlt cEnv (Alt p pt rhs) = Alt p pt (tsRhs cEnv rhs)

tsField :: CompilerEnv -> Field Expression -> Field Expression
tsField cEnv (Field p i e) = Field p i (tsExpr cEnv e)

-- ----------------------------------------------------------------------------
-- helper functions
-- ----------------------------------------------------------------------------

-- |looks up a given variable (from the given module!) in the value environment
lookupValue' :: ModuleIdent -> Ident -> ValueEnv -> ValueInfo
lookupValue' m id0 vEnv = 
  case filter (valInMdl m) vals of
    [v] -> v
    _ -> internalError "TypeSigs.lookupValue'"
  where
  vals = lookupValue id0 vEnv
  
-- |checks whether the given "ValueInfo" refers to an identifier from
-- the given module
valInMdl :: ModuleIdent -> ValueInfo -> Bool
valInMdl m v = fromJust (qidModule $ origName v) == m 

-- |converts a type to a type expression
fromType :: Type -> TypeExpr
fromType (TypeConstructor  tc tys) = ConstructorType tc tys'
  where tys' = map fromType tys
fromType (TypeVariable         tv) = VariableType
   (if tv >= 0 then identSupply !! tv else mkIdent ('_' : show (-tv)))
fromType (TypeConstrained   tys _) = fromType (head tys)
fromType (TypeArrow       ty1 ty2) =
  ArrowType (fromType ty1) (fromType ty2)
fromType (TypeSkolem            k) =
  VariableType $ mkIdent $ "_?" ++ show k
fromType (TypeRecord       fs rty) = RecordType
  (map (\ (l, ty) -> ([l], fromType ty)) fs)
  ((fromType . TypeVariable) `fmap` rty)
