{- |
    Module      :  $Header$
    Description :  Transformation of explicit type signatures
    Copyright   :  2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This transformation removes the context in all explicit type signatures 
    by inserting the appropriate dictionary types for each element of the context. 
    This is needed for the second type check that expects a program without
    any type class elements. 
-}


module Transformations.TypeSigs (transformTypeSigs) where

import Curry.Syntax.Type
import Env.ClassEnv
import Base.CurryTypes
import Curry.Base.Ident
import CompilerEnv

-- | transforms all type signatures (in explicit type signatures declarations
-- *and* in explicitely typed expressions (!)) by removing their contexts
-- and inserting types for the dictionaries.  
transformTypeSigs :: CompilerEnv -> Module -> Module
transformTypeSigs cEnv (Module m e i ds) = Module m e i (concatMap (tsDecl cEnv) ds)

tsDecl :: CompilerEnv -> Decl -> [Decl]
tsDecl _cEnv d@(InfixDecl   _ _ _ _) = [d]
tsDecl _cEnv d@(DataDecl    _ _ _ _) = [d]
tsDecl _cEnv d@(NewtypeDecl _ _ _ _) = [d]
tsDecl _cEnv d@(TypeDecl    _ _ _ _) = [d]

tsDecl  cEnv (TypeSig p ids (Context cx) ty) =
  [TypeSig p ids (Context []) newTySig]
  where
  classes = map (\(ContextElem cls _ _) -> cls) cx
  dictTys = dictTypes (classEnv cEnv) classes
  dictTys' = map fromType dictTys
  vars = map (\(ContextElem _ var _) -> var) cx
  -- Replace the class variable (always 0 in dictTys, ergo always 
  -- identSupply !! 0 in dictTys') with the variable given in the context.  
  -- TODO: Rename all other variables so that they don't overlap with other type 
  -- variables in the type signature AND/OR match the type variables from
  -- the dictionary type with type variables from the type signature. 
  -- As currently, no other type variables than the type variable of the class
  -- itself are allowed, this TODO is not yet necessary. 
  dictTys'' = zipWith (\var ty0 -> substId (classVar, var) ty0) vars dictTys'
  
  constrNewTySig [] sig = sig
  constrNewTySig (d:ds) sig = constrNewTySig ds (ArrowType d sig)
  
  newTySig = constrNewTySig (reverse dictTys'') ty

  classVar = identSupply !! 0
  
tsDecl  cEnv   (FunctionDecl p cty id0 i eqs) = [FunctionDecl p cty id0 i (map (tsEqu cEnv) eqs)]
tsDecl _cEnv d@(ForeignDecl    _ _ _ _ _) = [d]
tsDecl _cEnv d@(ExternalDecl         _ _) = [d]
tsDecl  cEnv   (PatternDecl p cty id0 pt rhs) = [PatternDecl p cty id0 pt (tsRhs cEnv rhs)]
tsDecl _cEnv d@(FreeDecl             _ _) = [d]
tsDecl _cEnv d@(ClassDecl      _ _ _ _ _) = [d]
tsDecl _cEnv d@(InstanceDecl _ _ _ _ _ _) = [d]

tsEqu :: CompilerEnv -> Equation -> Equation
tsEqu cEnv (Equation p lhs rhs) = Equation p lhs (tsRhs cEnv rhs)

tsRhs :: CompilerEnv -> Rhs -> Rhs
tsRhs cEnv (SimpleRhs p e ds) = SimpleRhs p (tsExpr cEnv e) (concatMap (tsDecl cEnv) ds)
tsRhs cEnv (GuardedRhs cs ds) = GuardedRhs (map (tsCondExpr cEnv) cs) (concatMap (tsDecl cEnv) ds)

tsCondExpr :: CompilerEnv -> CondExpr -> CondExpr
tsCondExpr cEnv (CondExpr p e1 e2) = CondExpr p (tsExpr cEnv e1) (tsExpr cEnv e2)

tsExpr :: CompilerEnv -> Expression -> Expression
tsExpr _cEnv e@(Literal _) = e
tsExpr _cEnv e@(Variable _ _) = e
tsExpr _cEnv e@(Constructor _) = e
tsExpr cEnv   (Paren e) = tsExpr cEnv e
-- TODO: handle type signature in typed expression!
tsExpr cEnv (Typed cty e cx t) = Typed cty (tsExpr cEnv e) cx t
tsExpr cEnv (Tuple sref es) = Tuple sref (map (tsExpr cEnv) es)
tsExpr cEnv (List sref es) = List sref (map (tsExpr cEnv) es)
tsExpr cEnv (ListCompr sref e ss) = ListCompr sref (tsExpr cEnv e) (map (tsStmt cEnv) ss)
tsExpr cEnv (EnumFrom e1) = EnumFrom (tsExpr cEnv e1)
tsExpr cEnv (EnumFromThen e1 e2) = EnumFromThen (tsExpr cEnv e1) (tsExpr cEnv e2)
tsExpr cEnv (EnumFromTo e1 e2) = EnumFromTo (tsExpr cEnv e1) (tsExpr cEnv e2)
tsExpr cEnv (EnumFromThenTo e1 e2 e3) = EnumFromThenTo (tsExpr cEnv e1) (tsExpr cEnv e2) (tsExpr cEnv e3)
tsExpr cEnv (UnaryMinus i e) = UnaryMinus i (tsExpr cEnv e)
tsExpr cEnv (Apply e1 e2) = Apply (tsExpr cEnv e1) (tsExpr cEnv e2)
tsExpr cEnv (InfixApply e1 op e2) = InfixApply (tsExpr cEnv e1) op (tsExpr cEnv e2)
tsExpr cEnv (LeftSection e op) = LeftSection (tsExpr cEnv e) op
tsExpr cEnv (RightSection op e) = RightSection op (tsExpr cEnv e)
tsExpr cEnv (Lambda sref ps e) = Lambda sref ps (tsExpr cEnv e)
tsExpr cEnv (Let ds e) = Let (concatMap (tsDecl cEnv) ds) (tsExpr cEnv e)
tsExpr cEnv (Do ss e) = Do (map (tsStmt cEnv) ss) (tsExpr cEnv e)
tsExpr cEnv (IfThenElse sref e1 e2 e3) = 
  IfThenElse sref (tsExpr cEnv e1) (tsExpr cEnv e2) (tsExpr cEnv e3)
tsExpr cEnv (Case sref ct e alts) = Case sref ct (tsExpr cEnv e) (map (tsAlt cEnv) alts)
tsExpr cEnv (RecordConstr fs) = RecordConstr (map (tsField cEnv) fs)
tsExpr cEnv (RecordSelection e i) = RecordSelection (tsExpr cEnv e) i
tsExpr cEnv (RecordUpdate fs e) = RecordUpdate (map (tsField cEnv) fs) (tsExpr cEnv e)


tsStmt :: CompilerEnv -> Statement -> Statement
tsStmt cEnv (StmtExpr sref e) = StmtExpr sref (tsExpr cEnv e)
tsStmt cEnv (StmtDecl ds) = StmtDecl (concatMap (tsDecl cEnv) ds)
tsStmt cEnv (StmtBind sref p e) = StmtBind sref p (tsExpr cEnv e)

tsAlt :: CompilerEnv -> Alt -> Alt
tsAlt cEnv (Alt p pt rhs) = Alt p pt (tsRhs cEnv rhs)

tsField :: CompilerEnv -> Field Expression -> Field Expression
tsField cEnv (Field p i e) = Field p i (tsExpr cEnv e)

-- ----------------------------------------------------------------------------
-- helper functions
-- ----------------------------------------------------------------------------

-- | Substitutes the class variable with the given variable. (TODO: Also renames
-- all other variables?)
substId :: (Ident, Ident) -> TypeExpr -> TypeExpr
substId s (ConstructorType qid tes) = ConstructorType qid (map (substId s) tes)
substId s (SpecialConstructorType tcon tes) = SpecialConstructorType tcon (map (substId s) tes)
substId (x, y) (VariableType i) 
  | x == i = VariableType y
  | otherwise = VariableType i -- VariableType (renameIdent i 1)  
substId s (TupleType tes) = TupleType (map (substId s) tes)
substId s (ListType te) = ListType (substId s te)
substId s (ArrowType te1 te2) = ArrowType (substId s te1) (substId s te2)
substId s (RecordType ts mt) = 
  RecordType (map (\(ids, te) -> (ids, substId s te)) ts)
             (fmap (substId s) mt)
