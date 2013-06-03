{- |
    Module      :  $Header$
    Description :  
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The main function of this module transforms the abstract syntax tree by
    adding dictionary parameters where necessary. 
-}

module Transformations.Dictionaries (insertDicts) where

import Curry.Base.Ident
import CompilerEnv
import Curry.Syntax
import Env.ClassEnv
import Base.Names (sep, mkSelFunName, mkDictName)
import Base.Messages
import Data.Maybe

import Base.Types as BT

import Control.Monad.State as S

-- ----------------------------------------------------------------------------
-- the state monad used
-- ----------------------------------------------------------------------------

type DI = S.State DIState

data DIState = DIState 
  { theClassEnv :: ClassEnv
  }

initState :: ClassEnv -> DIState
initState cEnv = DIState cEnv

runDI :: DI a -> DIState -> a
runDI comp init0 = let (a, _s) = S.runState comp init0 in a

getClassEnv :: DI ClassEnv
getClassEnv = S.gets theClassEnv

-- ----------------------------------------------------------------------------
-- the transformation functions
-- ----------------------------------------------------------------------------

-- |The main function of this module. It descends into the syntax tree and
-- inserts dictionary parameters (in function declarations and in expressions)
insertDicts :: Module -> CompilerEnv -> Module
insertDicts mdl cEnv = 
  runDI (diModule mdl) (initState $ classEnv cEnv)   

-- |convert a whole module
diModule :: Module -> DI Module
diModule (Module m e i ds) = Module m e i `liftM` (mapM diDecl ds)
  
-- |convert function declarations
-- TODO: pass constrained type from outer scope?
diDecl :: Decl -> DI Decl
diDecl (FunctionDecl p (Just cty) id0 eqs) = do
  cEnv <- getClassEnv
  let cty'  = mirror2CT cty
      -- we have to reduce the context before adding dictionary parameters, 
      -- because the recorded context is the "raw" context 
      cty'' = (reduceContext cEnv $ fst $ cty', snd cty')
  FunctionDecl p (Just cty) id0 `liftM` (mapM (diEqu cty'' $ show id0) eqs)
diDecl (FunctionDecl _ Nothing _ _) = internalError "no type info in diDecl"
-- TODO: convert pattern declarations!
diDecl f@(PatternDecl _p (Just _cty) _ps _rhs) = return f 
diDecl (PatternDecl _ Nothing _ _) = internalError "no type info in diDecl"
diDecl f = return f

-- |transform an equation
-- Takes the type of the corresponding function declaration, and the name
-- of the function 
diEqu :: ConstrType -> String -> Equation -> DI Equation
diEqu cty fun (Equation p lhs rhs)= 
  liftM2 (Equation p) (diLhs cty fun lhs) (diRhs cty fun rhs)

-- |transform right hand sides
diRhs :: ConstrType -> String -> Rhs -> DI Rhs
diRhs cty fun (SimpleRhs p e ds) = 
  liftM2 (SimpleRhs p) (diExpr cty fun e) (mapM diDecl ds)
diRhs cty fun (GuardedRhs ces ds) = 
  liftM2 GuardedRhs (mapM (diCondExpr cty fun) ces) (mapM diDecl ds)

  
-- | transform conditional expressions
diCondExpr :: ConstrType -> String -> CondExpr -> DI CondExpr
diCondExpr cty fun (CondExpr p e1 e2) = 
  liftM2 (CondExpr p) (diExpr cty fun e1) (diExpr cty fun e2)
  
-- | transform left hand sides
diLhs :: ConstrType -> String -> Lhs -> DI Lhs
diLhs cty fun (FunLhs id0 ps) = 
  return $ FunLhs id0 (dictParams ++ ps)  
  where 
  dictParams = map (VariablePattern . contextElemToVar fun) (fst cty)
diLhs cty fun (OpLhs p1 id0 p2) = diLhs cty fun (FunLhs id0 [p1, p2])
diLhs cty fun a@(ApLhs _ _) =
  let (f, ps) = flatLhs a
  in diLhs cty fun (FunLhs f ps)  

-- | transform expressions
diExpr :: ConstrType -> String -> Expression -> DI Expression
diExpr _ _ e@(Literal _) = return e
diExpr cty fun v@(Variable (Just varCty) qid) = do 
  codes <- abstrCode
  cEnv <- getClassEnv
  return $ foldl Apply (var'' cEnv) codes 
  where
  abstrCode = do
    cEnv <- getClassEnv
    let cx = mirror2Cx (fst varCty)
        codes = map (concreteCode fun . dictCode cEnv (fst cty)) cx 
    return codes
  maybeCls cEnv = lookupDefiningClass cEnv qid
  cls cEnv = fromJust $ maybeCls cEnv
  -- if we have a class function, transform this into the appropriate selector
  -- function
  var'' cEnv = if isNothing $ maybeCls cEnv 
    then v
    -- TODO: canonical class/function names
    else Variable (Just varCty) 
           (qualify $ mkIdent $ mkSelFunName (show $ cls cEnv) (show $ qid))
diExpr _ _ (Variable Nothing _) = internalError "diExpr: no type info"
diExpr _ _ e@(Constructor _) = return e
diExpr cty fun (Paren e) = Paren `liftM` diExpr cty fun e
diExpr cty fun (Typed e cx t) = liftM3 Typed (diExpr cty fun e) (return cx) (return t)
diExpr cty fun (Tuple sref es) = Tuple sref `liftM` (mapM (diExpr cty fun) es)   
diExpr cty fun (List srefs es) = List srefs `liftM` (mapM (diExpr cty fun) es)
diExpr cty fun (ListCompr sref e ss) = 
  liftM2 (ListCompr sref) (diExpr cty fun e) (mapM (diStmt cty fun) ss) 
diExpr cty fun (EnumFrom e1) = EnumFrom `liftM` (diExpr cty fun e1)
diExpr cty fun (EnumFromThen e1 e2) = 
  liftM2 EnumFromThen (diExpr cty fun e1) (diExpr cty fun e2)
diExpr cty fun (EnumFromTo e1 e2) = 
  liftM2 EnumFromTo (diExpr cty fun e1) (diExpr cty fun e2)
diExpr cty fun (EnumFromThenTo e1 e2 e3) = 
  liftM3 EnumFromThenTo (diExpr cty fun e1) (diExpr cty fun e2) (diExpr cty fun e3)
diExpr cty fun (UnaryMinus i e) = UnaryMinus i `liftM` diExpr cty fun e
diExpr cty fun (Apply e1 e2) = liftM2 Apply (diExpr cty fun e1) (diExpr cty fun e2)
-- adding dictionary parameters for the operator in InfixApply, Left- and RightSection
-- expressions by transforming them into a term with Variable's and Apply's where
-- the operator (or the flipped operator) is at the head position. 
-- Note that infixOp preserves the type annotation of the operator!
diExpr cty fun (InfixApply e1 op e2) = 
  diExpr cty fun (Apply (Apply (infixOp op) e1) e2)
diExpr cty fun (LeftSection e op) = 
  diExpr cty fun (Apply (infixOp op) e)
diExpr cty fun (RightSection op e) = 
  diExpr cty fun (Apply (Apply prelFlip (infixOp op)) e)
diExpr cty fun (Lambda sref ps e) = Lambda sref ps `liftM` diExpr cty fun e
-- TODO: pass constrained type from outer scope?
diExpr cty fun (Let ds e) = liftM2 Let (mapM diDecl ds) (diExpr cty fun e)
diExpr cty fun (Do ss e) = liftM2 Do (mapM (diStmt cty fun) ss) (diExpr cty fun e)
diExpr cty fun (IfThenElse s e1 e2 e3) = 
  liftM3 (IfThenElse s) (diExpr cty fun e1) (diExpr cty fun e2) (diExpr cty fun e3)
diExpr cty fun (Case s ct e alts) = 
  liftM2 (Case s ct) (diExpr cty fun e) (mapM (diAlt cty fun) alts)
diExpr cty fun (RecordConstr fs) = 
  RecordConstr `liftM` (mapM (diField cty fun) fs)
diExpr cty fun (RecordSelection e id0) = 
  flip RecordSelection id0 `liftM` diExpr cty fun e
diExpr cty fun (RecordUpdate fs e) = 
  liftM2 RecordUpdate (mapM (diField cty fun) fs) (diExpr cty fun e)
  

-- |transform statements
diStmt :: ConstrType -> String -> Statement -> DI Statement
diStmt cty fun (StmtExpr s e) = StmtExpr s `liftM` diExpr cty fun e
diStmt _   _ (StmtDecl ds) = StmtDecl `liftM` (mapM (diDecl) ds)
diStmt cty fun (StmtBind s p e) = StmtBind s p `liftM` diExpr cty fun e

-- |transform alts
diAlt :: ConstrType -> String -> Alt -> DI Alt
diAlt cty fun (Alt p pt rhs) = Alt p pt `liftM` (diRhs cty fun rhs)

-- |transform fields
diField :: ConstrType -> String -> Field Expression -> DI (Field Expression)
diField cty fun (Field p i e) = Field p i `liftM` diExpr cty fun e

-- |generates an identifier for the given function and context element
contextElemToVar:: String -> (QualIdent, Type) -> Ident
contextElemToVar _fun (cls, ty) =
  -- TODO: better name generation?
  flip renameIdent 1 $ mkIdent ({-fun ++ sep ++ -}show cls ++ sep ++ show ty)

-- creates concrete code from the abstract operations
concreteCode :: String -> Operation -> Expression
concreteCode fun (Dictionary d) = 
  var' $ contextElemToVar fun d
concreteCode fun (SelSuperClass d1 d2) =
  Apply (var sel) (var' $ contextElemToVar fun d1)
  where sel = mkSelFunName (show $ fst d1) (show $ fst d2)  
concreteCode fun (BuildDict (cls,ty) ops) = 
  foldl Apply (var $ mkDictName (show cls) (show ty'))
       (map (concreteCode fun) ops) 
  where 
  ty' = if not $ isCons ty then internalError "concreteCode"
        else fst $ fromJust $ splitType ty 


var :: String -> Expression
var = Variable Nothing . qualify . mkIdent

var' :: Ident -> Expression
var' = Variable Nothing . qualify

-- ---------------------------------------------------------------------------
-- helper functions
-- ---------------------------------------------------------------------------

type ConstrType = (BT.Context, Type)

tySchemeFlip :: ConstrType
-- the type of flip shouldn't be needed, hence the internalError 
tySchemeFlip = ([], internalError "tySchemeFlip")

prelFlip :: Expression
prelFlip = Variable (Just $ mirrorCT tySchemeFlip) $ preludeIdent "flip"

preludeIdent :: String -> QualIdent
preludeIdent = qualifyWith preludeMIdent . mkIdent
