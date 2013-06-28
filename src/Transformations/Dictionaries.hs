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
import Env.Value
import Base.Names (sep, mkSelFunName, mkDictName)
import Base.Messages
import Data.Maybe
import Base.Utils

import Base.Types as BT

import Control.Monad.State as S

-- ----------------------------------------------------------------------------
-- the state monad used
-- ----------------------------------------------------------------------------

type DI = S.State DIState

data DIState = DIState 
  { theClassEnv :: ClassEnv
  , theValueEnv :: ValueEnv
  }

initState :: ClassEnv -> ValueEnv -> DIState
initState cEnv vEnv = DIState cEnv vEnv 

runDI :: DI a -> DIState -> a
runDI comp init0 = let (a, _s) = S.runState comp init0 in a

getClassEnv :: DI ClassEnv
getClassEnv = S.gets theClassEnv

getValueEnv :: DI ValueEnv
getValueEnv = S.gets theValueEnv

-- ----------------------------------------------------------------------------
-- the transformation functions
-- ----------------------------------------------------------------------------

-- |The main function of this module. It descends into the syntax tree and
-- inserts dictionary parameters (in function declarations and in expressions)
insertDicts :: Module -> CompilerEnv -> Module
insertDicts mdl cEnv = 
  runDI (diModule mdl) (initState (classEnv cEnv) (valueEnv cEnv))

-- |convert a whole module
diModule :: Module -> DI Module
diModule (Module m e i ds) = Module m e i `liftM` (mapM (diDecl BT.emptyContext) ds)
  
-- |convert function declarations
-- pass context from outer scope
diDecl :: BT.Context -> Decl -> DI Decl
diDecl cx (FunctionDecl p (Just cty@(cx', _)) n id0 eqs) = do
  cEnv <- getClassEnv
  vEnv <- getValueEnv
  let -- we have to reduce the context before adding dictionary parameters, 
      -- because the recorded context is the "raw" context 
      cx'' = reduceContext cEnv $ mirror2Cx cx'
      cx''' = removeNonLocal vEnv id0 lookupValue cx''
  FunctionDecl p (Just cty) n id0 `liftM` (mapM (diEqu (cx ++ cx''') cx''') eqs)
diDecl _ (FunctionDecl _ Nothing _ _ _) = internalError "no type info in diDecl"

diDecl cx (PatternDecl p (Just cty) n pt rhs) = 
  PatternDecl p (Just cty) n pt `liftM` (diRhs cx rhs) 
diDecl _ (PatternDecl _ Nothing _ _ _) = internalError "no type info in diDecl"

diDecl _ f = return f

-- |removes context elements that are not local but refer to type variables from the
-- upper scopes, i.e., context elements that have a type with type variables
-- less than zero. 
removeNonLocal :: ValueEnv -> a -> (a -> ValueEnv -> [ValueInfo]) -> BT.Context -> BT.Context
removeNonLocal vEnv id0 lookup0 cx = newCx
  where
  Value _ _ (ForAll cxInf _ _) : _ = lookup0 id0 vEnv
  newCx = map snd $ filter (\(e1, _e2) -> local e1) $ zip' cxInf cx
  local :: (QualIdent, Type) -> Bool
  -- TODO: actually check only the type variable in head position... 
  local (_qid, ty) = all (>= 0) $ BT.typeVars ty

-- |transform an equation
-- Takes the type of the corresponding function declaration, and the name
-- of the function 
diEqu :: BT.Context -> BT.Context -> Equation -> DI Equation
diEqu cxAll cxLocal (Equation p lhs rhs)= 
  liftM2 (Equation p) (diLhs cxLocal lhs) (diRhs cxAll rhs)

-- |transform right hand sides
diRhs :: BT.Context -> Rhs -> DI Rhs
diRhs cx (SimpleRhs p e ds) = 
  liftM2 (SimpleRhs p) (diExpr cx e) (mapM (diDecl cx) ds)
diRhs cx (GuardedRhs ces ds) = 
  liftM2 GuardedRhs (mapM (diCondExpr cx) ces) (mapM (diDecl cx) ds)

  
-- | transform conditional expressions
diCondExpr :: BT.Context -> CondExpr -> DI CondExpr
diCondExpr cx (CondExpr p e1 e2) = 
  liftM2 (CondExpr p) (diExpr cx e1) (diExpr cx e2)
  
-- | transform left hand sides
diLhs :: BT.Context -> Lhs -> DI Lhs
diLhs cx (FunLhs id0 ps) = 
  return $ FunLhs id0 (dictParams ++ ps)  
  where 
  dictParams = map (VariablePattern . contextElemToVar) cx
diLhs cx (OpLhs p1 id0 p2) = diLhs cx (FunLhs id0 [p1, p2])
diLhs cx a@(ApLhs _ _) =
  let (f, ps) = flatLhs a
  in diLhs cx (FunLhs f ps)  

-- | transform expressions
diExpr :: BT.Context -> Expression -> DI Expression
diExpr _ e@(Literal _) = return e
diExpr cx0 v@(Variable (Just varCty0) qid) = do 
  codes <- abstrCode
  cEnv <- getClassEnv
  let code = foldl Apply (var'' cEnv) codes
  -- for nullary class methods add additional unit argument
  return $ if isClassMethod cEnv && zeroArity cEnv 
    then Apply code (Constructor qUnitId)
    else code
  where
  abstrCode = do
    cEnv <- getClassEnv
    vEnv <- getValueEnv
    let varCty = (removeNonLocal vEnv qid qualLookupValue $ mirror2Cx $ fst varCty0, snd varCty0)
        -- check whether we have a class method
        cx = if isNothing $ maybeCls cEnv then fst varCty else mirror2Cx $ fst varCty0
        codes = map (concreteCode . dictCode cEnv cx0) cx 
    return codes
  maybeCls cEnv = lookupDefiningClass cEnv qid
  cls cEnv = fromJust $ maybeCls cEnv
  -- if we have a class function, transform this into the appropriate selector
  -- function
  isClassMethod cEnv = isJust $ maybeCls cEnv
  zeroArity cEnv = (arrowArity $ typeSchemeToType $ 
    fromJust $ lookupMethodTypeScheme' cEnv (cls cEnv) (unqualify qid)) == 0
  var'' cEnv = if not $ isClassMethod cEnv 
    then v
    -- Unqualify "qid"! The name of the selection function is still unique
    -- because the class name is unique 
    else Variable (Just varCty0) 
           (qualify $ mkIdent $ mkSelFunName (show $ cls cEnv) (show $ unqualify $ qid))
diExpr _ (Variable Nothing _) = internalError "diExpr: no type info"
diExpr _ e@(Constructor _) = return e
diExpr cx (Paren e) = Paren `liftM` diExpr cx e
diExpr cx (Typed cty e cxt t) = liftM3 (Typed cty) (diExpr cx e) (return cxt) (return t)
diExpr cx (Tuple sref es) = Tuple sref `liftM` (mapM (diExpr cx) es)   
diExpr cx (List srefs es) = List srefs `liftM` (mapM (diExpr cx) es)
diExpr cx (ListCompr sref e ss) = 
  liftM2 (ListCompr sref) (diExpr cx e) (mapM (diStmt cx) ss) 
diExpr cx (EnumFrom e1) = EnumFrom `liftM` (diExpr cx e1)
diExpr cx (EnumFromThen e1 e2) = 
  liftM2 EnumFromThen (diExpr cx e1) (diExpr cx e2)
diExpr cx (EnumFromTo e1 e2) = 
  liftM2 EnumFromTo (diExpr cx e1) (diExpr cx e2)
diExpr cx (EnumFromThenTo e1 e2 e3) = 
  liftM3 EnumFromThenTo (diExpr cx e1) (diExpr cx e2) (diExpr cx e3)
diExpr cx (UnaryMinus i e) = UnaryMinus i `liftM` diExpr cx e
diExpr cx (Apply e1 e2) = liftM2 Apply (diExpr cx e1) (diExpr cx e2)
-- adding dictionary parameters for the operator in InfixApply, Left- and RightSection
-- expressions by transforming them into a term with Variable's and Apply's where
-- the operator (or the flipped operator) is at the head position. 
-- Note that infixOp preserves the type annotation of the operator!
diExpr cx (InfixApply e1 op e2) = 
  diExpr cx (Apply (Apply (infixOp op) e1) e2)
diExpr cx (LeftSection e op) = 
  diExpr cx (Apply (infixOp op) e)
diExpr cx (RightSection op e) = 
  diExpr cx (Apply (Apply prelFlip (infixOp op)) e)
diExpr cx (Lambda sref ps e) = Lambda sref ps `liftM` diExpr cx e
-- pass context from outer scope
diExpr cx (Let ds e) = liftM2 Let (mapM (diDecl cx) ds) (diExpr cx e)
diExpr cx (Do ss e) = liftM2 Do (mapM (diStmt cx) ss) (diExpr cx e)
diExpr cx (IfThenElse s e1 e2 e3) = 
  liftM3 (IfThenElse s) (diExpr cx e1) (diExpr cx e2) (diExpr cx e3)
diExpr cx (Case s ct e alts) = 
  liftM2 (Case s ct) (diExpr cx e) (mapM (diAlt cx) alts)
diExpr cx (RecordConstr fs) = 
  RecordConstr `liftM` (mapM (diField cx) fs)
diExpr cx (RecordSelection e id0) = 
  flip RecordSelection id0 `liftM` diExpr cx e
diExpr cx (RecordUpdate fs e) = 
  liftM2 RecordUpdate (mapM (diField cx) fs) (diExpr cx e)
  

-- |transform statements
diStmt :: BT.Context -> Statement -> DI Statement
diStmt cx (StmtExpr s e) = StmtExpr s `liftM` diExpr cx e
diStmt cx (StmtDecl ds) = StmtDecl `liftM` (mapM (diDecl cx) ds)
diStmt cx (StmtBind s p e) = StmtBind s p `liftM` diExpr cx e

-- |transform alts
diAlt :: BT.Context -> Alt -> DI Alt
diAlt cx (Alt p pt rhs) = Alt p pt `liftM` (diRhs cx rhs)

-- |transform fields
diField :: BT.Context -> Field Expression -> DI (Field Expression)
diField cx (Field p i e) = Field p i `liftM` diExpr cx e

-- |generates an identifier for the given function and context element
contextElemToVar:: (QualIdent, Type) -> Ident
contextElemToVar (cls, ty) =
  -- TODO: better name generation?
  flip renameIdent 1 $ 
    mkIdent (identPrefix ++ show cls ++ sep ++ show ty)

-- creates concrete code from the abstract operations
concreteCode :: Operation -> Expression
concreteCode (Dictionary d) = 
  var' $ contextElemToVar d
concreteCode (SelSuperClass d1 d2) =
  Apply (var sel) (var' $ contextElemToVar d1)
  where sel = mkSelFunName (show $ fst d1) (show $ fst d2)  
concreteCode (BuildDict (cls,ty) ops) = 
  foldl Apply (var $ mkDictName (show cls) (show ty'))
       (map concreteCode ops) 
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
-- the type of flip shouldn't be needed
tySchemeFlip = ([], TypeVariable 0)

prelFlip :: Expression
prelFlip = Variable (Just $ mirrorCT tySchemeFlip) $ preludeIdent "flip"

preludeIdent :: String -> QualIdent
preludeIdent = qualifyWith preludeMIdent . mkIdent
