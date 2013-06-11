{- |
    Module      :  $Header$
    Description :  Removal of type signatures
    Copyright   :  2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The transformation contained in this module removes all
    type signatures from the module that have non-empty contexts. 
    This is necessary for the second type check, that expects a program
    without any type classes elements.  
-}


module Transformations.TypeSigs (removeTypeSigs) where

import Curry.Syntax.Type

removeTypeSigs :: Module -> Module
removeTypeSigs (Module m e i ds) = Module m e i (concatMap tsDecl ds)

tsDecl :: Decl -> [Decl]
tsDecl d@(InfixDecl   _ _ _ _) = [d]
tsDecl d@(DataDecl    _ _ _ _) = [d]
tsDecl d@(NewtypeDecl _ _ _ _) = [d]
tsDecl d@(TypeDecl    _ _ _ _) = [d]
-- remove type signatures if their context is not empty
tsDecl d@(TypeSig _ _ (Context [])    _) = [d]
tsDecl   (TypeSig _ _ (Context (_:_)) _) = []
tsDecl   (FunctionDecl p cty n i eqs) = [FunctionDecl p cty n i (map tsEqu eqs)]
tsDecl d@(ForeignDecl    _ _ _ _ _) = [d]
tsDecl d@(ExternalDecl         _ _) = [d]
tsDecl   (PatternDecl p cty n pt rhs) = [PatternDecl p cty n pt (tsRhs rhs)]
tsDecl d@(FreeDecl             _ _) = [d]
tsDecl d@(ClassDecl      _ _ _ _ _) = [d]
tsDecl d@(InstanceDecl _ _ _ _ _ _) = [d]

tsEqu :: Equation -> Equation
tsEqu (Equation p lhs rhs) = Equation p lhs (tsRhs rhs)

tsRhs :: Rhs -> Rhs
tsRhs (SimpleRhs p e ds) = SimpleRhs p (tsExpr e) (concatMap tsDecl ds)
tsRhs (GuardedRhs cs ds) = GuardedRhs (map tsCondExpr cs) (concatMap tsDecl ds)

tsCondExpr :: CondExpr -> CondExpr
tsCondExpr (CondExpr p e1 e2) = CondExpr p (tsExpr e1) (tsExpr e2)

tsExpr :: Expression -> Expression
tsExpr e@(Literal _) = e
tsExpr e@(Variable _ _) = e
tsExpr e@(Constructor _) = e
tsExpr   (Paren e) = tsExpr e
-- TODO: handle type signature in typed expression!
tsExpr (Typed cty e cx t) = Typed cty (tsExpr e) cx t
tsExpr (Tuple sref es) = Tuple sref (map tsExpr es)
tsExpr (List sref es) = List sref (map tsExpr es)
tsExpr (ListCompr sref e ss) = ListCompr sref (tsExpr e) (map tsStmt ss)
tsExpr (EnumFrom e1) = EnumFrom (tsExpr e1)
tsExpr (EnumFromThen e1 e2) = EnumFromThen (tsExpr e1) (tsExpr e2)
tsExpr (EnumFromTo e1 e2) = EnumFromTo (tsExpr e1) (tsExpr e2)
tsExpr (EnumFromThenTo e1 e2 e3) = EnumFromThenTo (tsExpr e1) (tsExpr e2) (tsExpr e3)
tsExpr (UnaryMinus i e) = UnaryMinus i (tsExpr e)
tsExpr (Apply e1 e2) = Apply (tsExpr e1) (tsExpr e2)
tsExpr (InfixApply e1 op e2) = InfixApply (tsExpr e1) op (tsExpr e2)
tsExpr (LeftSection e op) = LeftSection (tsExpr e) op
tsExpr (RightSection op e) = RightSection op (tsExpr e)
tsExpr (Lambda sref ps e) = Lambda sref ps (tsExpr e)
tsExpr (Let ds e) = Let (concatMap tsDecl ds) (tsExpr e)
tsExpr (Do ss e) = Do (map tsStmt ss) (tsExpr e)
tsExpr (IfThenElse sref e1 e2 e3) = 
  IfThenElse sref (tsExpr e1) (tsExpr e2) (tsExpr e3)
tsExpr (Case sref ct e alts) = Case sref ct (tsExpr e) (map tsAlt alts)
tsExpr (RecordConstr fs) = RecordConstr (map tsField fs)
tsExpr (RecordSelection e i) = RecordSelection (tsExpr e) i
tsExpr (RecordUpdate fs e) = RecordUpdate (map tsField fs) (tsExpr e)


tsStmt :: Statement -> Statement
tsStmt (StmtExpr sref e) = StmtExpr sref (tsExpr e)
tsStmt (StmtDecl ds) = StmtDecl (concatMap tsDecl ds)
tsStmt (StmtBind sref p e) = StmtBind sref p (tsExpr e)

tsAlt :: Alt -> Alt
tsAlt (Alt p pt rhs) = Alt p pt (tsRhs rhs)

tsField :: Field Expression -> Field Expression
tsField (Field p i e) = Field p i (tsExpr e)

