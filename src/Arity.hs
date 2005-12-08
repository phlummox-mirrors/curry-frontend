-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- Arity - In order to generate correct FlatCurry applications it is necessary
--         to define the arity of a function or a constructor as the number 
--         of its arguments (instead of using the arity computed from the
--         type). For this reason this module provides functions for
--         dealing with arity environment.
--
-- December 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module Arity (ArityEnv, ArityInfo(..),
	      bindArities, bindImportArities,
	      bindArity, qualLookupArity,
	      initAEnv) where

import Base
import CurrySyntax
import Ident
import Env
import Utils
import Maybe
import List


-------------------------------------------------------------------------------

-- Expands the arity envorinment with (global / local) function arities and
-- constructor arities
bindArities :: ArityEnv -> Module -> ArityEnv
bindArities aEnv (Module mid _ decls)
   = foldl (visitDecl mid) aEnv decls

--
bindImportArities :: ModuleEnv -> ArityEnv -> Module -> ArityEnv
bindImportArities mEnv aEnv (Module _ _ decls)
   = foldl (bindImport mEnv) aEnv decls
 where
 bindImport mEnv aEnv (ImportDecl pos mid qual asMid ispec)
    = maybe (internalError "Arity.bindImportArities")
            (foldl (visitIDecl mid) aEnv)
	    (lookupModule mid mEnv)
 bindImport mEnv aEnv _ = aEnv

--
bindArity :: ModuleIdent -> Ident -> Int -> ArityEnv -> ArityEnv
bindArity mid id a aEnv
   = bindEnv id'
             (insertArity arity idArities)
	     (bindEnv qid (insertArity arity qidArities) aEnv)
  -- | uniqueId id == 0
  --   = bindEnv id' 
  --             (insertArity arity idArities) 
  --             (bindEnv qid (insertArity arity qidArities) aEnv)
  -- | otherwise
  --   = bindEnv id' (insertArity arity idArities) aEnv
 where
 id' = qualify id
 qid = qualifyWith mid id
 arity = ArityInfo qid a
 idArities = fromMaybe [] (lookupEnv id' aEnv)
 qidArities = fromMaybe [] (lookupEnv qid aEnv)

--
--lookupArity :: Ident -> ArityEnv -> [ArityInfo]
--lookupArity id aEnv = qualLookupArity (qualify id) aEnv

--
qualLookupArity :: QualIdent -> ArityEnv -> [ArityInfo]
qualLookupArity qid aEnv = fromMaybe [] (lookupEnv qid aEnv)
			   ++! qualLookupConsArity qid aEnv
			   ++! lookupTupleArity (unqualify qid)
--
initAEnv :: ArityEnv
initAEnv
   = foldr (\ (id,arity) -> bindArity preludeMIdent id arity) 
           emptyEnv 
	   predefArities
 where
 predefArities = [(unitId, 0),
		  (nilId,  0),
		  (consId, 2)
		 ]

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

type ArityEnv = Env QualIdent [ArityInfo]

data ArityInfo = ArityInfo QualIdent Int deriving Show

-------------------------------------------------------------------------------

visitDecl :: ModuleIdent -> ArityEnv -> Decl -> ArityEnv
visitDecl mid aEnv (DataDecl _ _ _ cdecls)
   = foldl (visitConstrDecl mid) aEnv cdecls
visitDecl mid aEnv (ExternalDecl _ _ _ id texpr)
   = bindArity mid id (typeArity texpr) aEnv
visitDecl mid aEnv (FunctionDecl _ id equs)
   = let (Equation _ lhs rhs) = head equs
     in  visitRhs mid (visitLhs mid id aEnv lhs) rhs
visitDecl _ aEnv _ = aEnv


visitConstrDecl :: ModuleIdent -> ArityEnv -> ConstrDecl -> ArityEnv
visitConstrDecl mid aEnv (ConstrDecl _ _ id texprs)
   = bindArity mid id (length texprs) aEnv
visitConstrDecl mid aEnv (ConOpDecl _ _ _ id _)
   = bindArity mid id 2 aEnv


visitLhs :: ModuleIdent -> Ident -> ArityEnv -> Lhs -> ArityEnv
visitLhs mid _ aEnv (FunLhs id params)
   = bindArity mid id (length params) aEnv
visitLhs mid id aEnv (OpLhs _ _ _)
   = bindArity mid id 2 aEnv
visitLhs _ _ aEnv _ = aEnv


visitRhs :: ModuleIdent -> ArityEnv -> Rhs -> ArityEnv
visitRhs mid aEnv (SimpleRhs _ expr decls)
   = foldl (visitDecl mid) (visitExpression mid aEnv expr) decls
visitRhs mid aEnv (GuardedRhs cexprs decls)
   = foldl (visitDecl mid) (foldl (visitCondExpr mid) aEnv cexprs) decls


visitCondExpr :: ModuleIdent -> ArityEnv -> CondExpr -> ArityEnv
visitCondExpr mid aEnv (CondExpr _ cond expr)
   = visitExpression mid (visitExpression mid aEnv expr) cond


visitExpression :: ModuleIdent -> ArityEnv -> Expression -> ArityEnv
visitExpression mid aEnv (Paren expr)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (Typed expr _)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (Tuple exprs)
   = foldl (visitExpression mid) aEnv exprs
visitExpression mid aEnv (List exprs)
   = foldl (visitExpression mid) aEnv exprs
visitExpression mid aEnv (ListCompr expr stmts)
   = foldl (visitStatement mid) (visitExpression mid aEnv expr) stmts
visitExpression mid aEnv (EnumFrom expr)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (EnumFromThen expr1 expr2)
   = foldl (visitExpression mid) aEnv [expr1,expr2]
visitExpression mid aEnv (EnumFromTo expr1 expr2)
   = foldl (visitExpression mid) aEnv [expr1,expr2]
visitExpression mid aEnv (EnumFromThenTo expr1 expr2 expr3)
   = foldl (visitExpression mid) aEnv [expr1,expr2,expr3]
visitExpression mid aEnv (UnaryMinus _ expr)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (Apply expr1 expr2)
   = foldl (visitExpression mid) aEnv [expr1,expr2]
visitExpression mid aEnv (InfixApply expr1 _ expr2)
   = foldl (visitExpression mid) aEnv [expr1,expr2]
visitExpression mid aEnv (LeftSection expr _)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (RightSection _ expr)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (Lambda _ expr)
   = visitExpression mid aEnv expr
visitExpression mid aEnv (Let decls expr)
   = foldl (visitDecl mid) (visitExpression mid aEnv expr) decls
visitExpression mid aEnv (Do stmts expr)
   = foldl (visitStatement mid) (visitExpression mid aEnv expr) stmts
visitExpression mid aEnv (IfThenElse expr1 expr2 expr3)
   = foldl (visitExpression mid) aEnv [expr1,expr2,expr3]
visitExpression mid aEnv (Case expr alts)
   = visitExpression mid (foldl (visitAlt mid) aEnv alts) expr
visitExpression _ aEnv _ = aEnv


visitStatement :: ModuleIdent -> ArityEnv -> Statement -> ArityEnv
visitStatement mid aEnv (StmtExpr expr)
   = visitExpression mid aEnv expr
visitStatement mid aEnv (StmtDecl decls)
   = foldl (visitDecl mid) aEnv decls
visitStatement mid aEnv (StmtBind _ expr)
   = visitExpression mid aEnv expr


visitAlt :: ModuleIdent -> ArityEnv -> Alt -> ArityEnv
visitAlt mid aEnv (Alt _ _ rhs)
   = visitRhs mid aEnv rhs


visitIDecl :: ModuleIdent -> ArityEnv -> IDecl -> ArityEnv
visitIDecl mid aEnv (IDataDecl _ qid _ mcdecls)
   = foldl (visitConstrDecl (fromMaybe mid mmid)) aEnv (catMaybes mcdecls)
 where (mmid, _) = splitQualIdent qid
visitIDecl mid aEnv (IFunctionDecl _ qid arity _)
   = bindArity (fromMaybe mid mmid) id arity aEnv
 where (mmid, id) = splitQualIdent qid
visitIDecl _ aEnv _ = aEnv


-------------------------------------------------------------------------------

-- Computes the function arity using a type expression
typeArity :: TypeExpr -> Int
typeArity (ArrowType _ t2) = 1 + typeArity t2
typeArity _                = 0

--
qualLookupConsArity :: QualIdent -> ArityEnv -> [ArityInfo]
qualLookupConsArity qid aEnv
   | maybe False ((==) consId) id'
     = fromMaybe [] (lookupEnv (qualify id) aEnv)
   | otherwise
     = []
   -- | (maybe False ((==) preludeMIdent) mmid) && (id == consId)
   --   = fromMaybe [] (lookupEnv (qualify id) aEnv)
   -- | otherwise
   --   = []
 where (mmid, id) = splitQualIdent qid
       id' = localIdent preludeMIdent qid

--
lookupTupleArity :: Ident -> [ArityInfo]
lookupTupleArity id
   | isTupleId id = [ArityInfo (qualifyWith preludeMIdent id) (tupleArity id)]
   | otherwise    = []


--
equArity :: ArityInfo -> ArityInfo -> Bool
equArity (ArityInfo qid1 _) (ArityInfo qid2 _) = qid1 == qid2

--
insertArity :: ArityInfo -> [ArityInfo] -> [ArityInfo]
insertArity arity as | any (equArity arity) as = as
		     | otherwise               = arity:as


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
