{- |
    Module      :  $Header$
    Description :  
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The main function of this module transforms the abstract syntax tree by
    adding dictionary parameters where necessary. This is actually not a
    check, but a transformation - but it can produce errors, so we include
    it as a check. 
-}

module Checks.Dictionaries (insertDicts) where

import Curry.Base.Ident
import CompilerEnv
import Curry.Syntax
import Curry.Base.Position
import Env.ClassEnv
import Env.Value
import Base.Names (mkSelFunName, mkDictName)
import Base.Messages
import Base.Utils
import Base.Types as BT
import Base.Idents (flipQIdent, tcPreludeEnumFromQIdent, tcPreludeEnumFromThenQIdent
                   , tcPreludeEnumFromToQIdent, tcPreludeEnumFromThenToQIdent)
import CompilerOpts

import Text.PrettyPrint hiding (sep)
import Data.Maybe
import Control.Monad.State as S

-- ----------------------------------------------------------------------------
-- the state monad used
-- ----------------------------------------------------------------------------

type DI = S.State DIState

data DIState = DIState 
  { mdl         :: ModuleIdent
  , theClassEnv :: ClassEnv
  , theValueEnv :: ValueEnv
  , typeClassExts :: Bool
  , errors      :: [Message]
  }

initState :: ModuleIdent -> ClassEnv -> ValueEnv -> Bool -> DIState
initState m cEnv vEnv repl = DIState m cEnv vEnv repl []

runDI :: DI a -> DIState -> (a, [Message])
runDI comp init0 = let (a, s) = S.runState comp init0 in (a, reverse $ errors s)

getClassEnv :: DI ClassEnv
getClassEnv = S.gets theClassEnv

getValueEnv :: DI ValueEnv
getValueEnv = S.gets theValueEnv

getModuleIdent :: DI ModuleIdent
getModuleIdent = S.gets mdl

typeClassExtensions :: DI Bool
typeClassExtensions = S.gets typeClassExts

ok :: DI ()
ok = return ()

report :: Message -> DI ()
report err = S.modify (\ s -> s { errors = err : errors s })

-- ----------------------------------------------------------------------------
-- the transformation functions
-- ----------------------------------------------------------------------------

-- |The main function of this module. It descends into the syntax tree and
-- inserts dictionary parameters (in function declarations and in expressions)
insertDicts :: Module -> CompilerEnv -> Options -> (Module, [Message])
insertDicts mdl'@(Module m _ _ _) cEnv opts = 
  runDI (diModule mdl') 
        (initState m (classEnv cEnv) (valueEnv cEnv) 
                     (TypeClassExtensions `elem` optExtensions opts))

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
      cx'' = reduceContext cEnv $ mirrorBFCx cx'
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
  Value _ _ (ForAll cxInf _ _) _ : _ = lookup0 id0 vEnv
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
  checkForAmbiguousInstances (qidPosition qid) (mirrorBFCx $ fst varCty0)
  cEnv <- getClassEnv
  vEnv <- getValueEnv
  m <- getModuleIdent
  
  let 
    abstrCode = do
      let varCty = (removeNonLocal vEnv qid qualLookupValue $ mirrorBFCx $ fst varCty0, snd varCty0)
          -- check whether we have a class method
          cx = if isNothing $ maybeCls then fst varCty else mirrorBFCx $ fst varCty0
          codes = map (concreteCode . dictCode cEnv cx0) cx 
      return codes
    maybeCls = case qualLookupValue qid vEnv of
      [Value _ _ _ cls'] -> cls'
      _ -> case qualLookupValue (qualQualify m qid) vEnv of
        [Value _ _ _ cls'] -> cls'
        _ -> internalError ("no function/method in Dictionaries: " ++ show qid) 
    cls = fromJust $ maybeCls
    -- if we have a class function, transform this into the appropriate selector
    -- function
    isClassMethod = isJust $ maybeCls
    zeroArity  = (arrowArity $ typeSchemeToType $ 
      fromJust $ canonLookupMethodTypeScheme' cEnv cls (unqualify qid)) == 0
    var'' = if not isClassMethod 
      then v
      -- Unqualify "qid"! The name of the selection function is still unique
      -- because the class name is unique 
      else Variable (Just varCty0) 
             (qualify $ mkIdent $ mkSelFunName (show cls) (show $ unqualify $ qid))
             
  
  case (isClassMethod && isNothing (canonLookupMethodTypeScheme' cEnv cls (unqualify qid))) of
    True -> do
      report $ errClassNeeded (qidPosition qid) cls
      return v
    False -> do 
      codes <- abstrCode   
      let code = foldl Apply var'' codes
      -- for nullary class methods add additional unit argument
      return $ if isClassMethod && zeroArity 
        then Apply code (Constructor qUnitId)
        else code
      
  
diExpr _ (Variable Nothing _) = internalError "diExpr: no type info"
diExpr _ e@(Constructor _) = return e
diExpr cx (Paren e) = Paren `liftM` diExpr cx e
diExpr cx (Typed cty e cxt t) = liftM3 (Typed cty) (diExpr cx e) (return cxt) (return t)
diExpr cx (Tuple sref es) = Tuple sref `liftM` (mapM (diExpr cx) es)   
diExpr cx (List srefs es) = List srefs `liftM` (mapM (diExpr cx) es)
diExpr cx (ListCompr sref e ss) = 
  liftM2 (ListCompr sref) (diExpr cx e) (mapM (diStmt cx) ss) 
diExpr cx (EnumFrom cty e1) = do
  exts <- typeClassExtensions
  case exts of
    False -> EnumFrom cty `liftM` (diExpr cx e1) 
    True -> diExpr cx (Apply (Variable cty tcPreludeEnumFromQIdent) e1)
diExpr cx (EnumFromThen cty e1 e2) = do
  exts <- typeClassExtensions
  case exts of
    False -> liftM2 (EnumFromThen cty) (diExpr cx e1) (diExpr cx e2)
    True -> diExpr cx (Apply (Apply (Variable cty tcPreludeEnumFromThenQIdent) e1) e2)
diExpr cx (EnumFromTo cty e1 e2) = do
  exts <- typeClassExtensions
  case exts of
    False -> liftM2 (EnumFromTo cty) (diExpr cx e1) (diExpr cx e2)
    True -> diExpr cx (Apply (Apply (Variable cty tcPreludeEnumFromToQIdent) e1) e2)
diExpr cx (EnumFromThenTo cty e1 e2 e3) = do
  exts <- typeClassExtensions
  case exts of
    False -> liftM3 (EnumFromThenTo cty) (diExpr cx e1) (diExpr cx e2) (diExpr cx e3)
    True -> diExpr cx (Apply (Apply (Apply (Variable cty tcPreludeEnumFromThenToQIdent) e1) e2) e3)
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

-- |looks whether there are context elements for which exist more than one
-- possible instance that could be applied
checkForAmbiguousInstances :: Position -> BT.Context -> DI ()
checkForAmbiguousInstances p = mapM_ check
  where
  check :: (QualIdent, Type) -> DI ()
  check (_cls, TypeVariable _) = ok
  check (cls,  TypeConstructor ty _) = do
    cEnv <- getClassEnv
    let insts = getInstances cEnv cls ty
    case insts of
      [] -> report $ errNoInstance p cls ty
      [_] -> ok
      (_:_:_) -> report $ errAmbiguousInstance p cls ty
  check (cls,  TypeConstrained (t:_) _) = check (cls, t)
  check (_cls, TypeConstrained [] _) = internalError "typeconstrained empty"
  check (cls,  TypeArrow _ty1 _ty2) = check (cls, TypeConstructor qArrowIdP [])
  check (_cls, TypeSkolem _) = internalError "typeSklolem"
  check (_cls, TypeRecord _ _) = internalError "typerecord"
      


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
prelFlip = Variable (Just $ mirrorFBCT tySchemeFlip) flipQIdent

-- ---------------------------------------------------------------------------
-- error messages
-- ---------------------------------------------------------------------------

errNoInstance :: Position -> QualIdent -> QualIdent -> Message
errNoInstance p cls ty = posMessage p $ 
  text "No instance for the class" <+> text (show cls) <+> text "and the type"
  <+> text (show ty)  

errAmbiguousInstance :: Position -> QualIdent -> QualIdent -> Message
errAmbiguousInstance p cls ty = posMessage p $ 
  text "Ambiguous instance use: " $$ 
  text "More than one instance applicable for the class" <+> 
  text (show cls) <+> text "and the type" <+> text (show ty)

errClassNeeded :: Position -> QualIdent -> Message
errClassNeeded p cls = posMessage p $ 
  text "class" <+> text (show cls) <+> 
  text "needed but not found. Import TCPrelude to fix this error. "
