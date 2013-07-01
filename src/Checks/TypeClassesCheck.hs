{- |
    Module      :  $Header$
    Description :  Type class related checks
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This file contains a lot of checks for typeclass elements (classes, 
    instances, contexts). It also contains transformation functions for
    the instance and class declarations. 
-}

module Checks.TypeClassesCheck (typeClassesCheck) where

import Curry.Syntax.Type as ST hiding (IDecl)
import Env.ClassEnv
import Env.TypeConstructor
import Base.Messages (Message, message, posMessage, internalError)

import Data.List
import Text.PrettyPrint hiding (sep)
import Data.Maybe
import Control.Monad.State

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax.Utils
import Curry.Syntax.Pretty
import Base.CurryTypes
import Base.Types as BT (TypeScheme, polyType, constrainBy, Type (..))
import qualified Base.Types as BTC (Context) 
import Base.SCC
import Base.Utils (findMultiples, fst3)
import Base.Names
import Base.TopEnv

import Checks.TypeCheck

-- ---------------------------------------------------------------------------
-- The state monad used (for gathering error messages)
-- ---------------------------------------------------------------------------

data TccState = TccState { errors :: [Message] }

type Tcc = State TccState

initTccState :: TccState
initTccState = TccState []

report :: Message -> Tcc ()
report w = modify $ \ s -> s { errors = w : errors s }

ok :: Tcc ()
ok = return ()

runTcc :: Tcc a -> TccState -> (a, [Message])
runTcc tcc s = let (a, s') = runState tcc s in (a, reverse $ errors s')

hasError :: Tcc Bool
hasError = liftM (not . null) $ gets errors

-- ---------------------------------------------------------------------------
-- main function
-- ---------------------------------------------------------------------------

-- |Checks class and instance declarations and removes these declarations; 
-- adds new data types/functions for the class and instance declarations. 
-- Also builds a corresponding class environment. 
typeClassesCheck :: ModuleIdent -> [Decl] -> ClassEnv -> TCEnv -> ([Decl], ClassEnv, [Message])
typeClassesCheck m decls (ClassEnv importedClasses importedInstances classMethodsMap) tcEnv0 = 
  case runTcc tcCheck initTccState of 
    ((newClasses, instances), []) -> 
      let newDecls = adjustContexts cEnv $ concatMap (transformInstance m cEnv tcEnv) $ 
            concatMap (transformClass2 cEnv) decls
          newClasses' = map (buildTypeSchemes m tcEnv 
                          . renameTypeSigVars) newClasses
          allClassesEnv = bindAll newClasses' importedClasses
          newClassMethodsMap = bindClassMethods m (allLocalClasses allClassesEnv) classMethodsMap
          cEnv = ClassEnv allClassesEnv instances newClassMethodsMap
      in (newDecls, cEnv, [])
    (_, errs@(_:_)) -> (decls, ClassEnv emptyTopEnv [] emptyTopEnv, errs)
  where
    classDecls = filter isClassDecl decls
    instDecls = filter isInstanceDecl decls
    typeSigs = gatherTypeSigs decls
    tcEnv = foldr (bindTC m tcEnv) tcEnv0 decls
    tcCheck = do
      phase1
      hasErr1 <- hasError
      case hasErr1 of
        True -> return ([], [])
        False -> do
          phase2
          hasErr2 <- hasError
          case hasErr2 of
            True -> return ([], [])
            False -> do
              phase3
    -- ----------------------------------------------------------------------
    -- phase 1: checks that don't need the class environment
    -- ----------------------------------------------------------------------
    phase1 = do
      mapM_ typeVariableInContext classDecls
      mapM_ classMethodSigsContainTypeVar classDecls
      mapM_ instanceTypeVarsDoNotAppearTwice instDecls
      
      -- currently disabled
      when False $ mapM_ checkCorrectTypeVarsInTypeSigs classDecls
      
      -- mapM_ checkTypeVarsInContext classDecls -- checked above (typeVariableInContext)
      mapM_ checkTypeVarsInContext instDecls
      mapM_ checkTypeVarsInContext typeSigs 
      
      mapM_ (checkInstanceDataTypeCorrect tcEnv) instDecls
      
      checkForDuplicateClassNames classDecls
      
      mapM_ (checkForDirectCycle m) classDecls
      
      noDoubleClassMethods m classDecls
    
    -- ----------------------------------------------------------------------
    -- phase 2: Checks that need the class environment, but mostly only for
    --          determining whether a given class exists or not. Qualified
    --          instance/superclass contexts are not yet needed. 
    -- ----------------------------------------------------------------------
    phase2 = do 
      let newClasses = map (classDeclToClass m) classDecls
          instances = map (instanceDeclToInstance m tcEnv) instDecls 
                      ++ importedInstances
          newClassEnv = ClassEnv (bindAll newClasses importedClasses) instances emptyTopEnv
      
      -- TODO: check also contexts of (imported) classes and interfaces?
      mapM_ (checkClassesInContext m newClassEnv) classDecls
      mapM_ (checkClassesInContext m newClassEnv) instDecls
      -- check also contexts in typed expressions
      mapM_ (checkClassesInContext m newClassEnv) typeSigs
          
      mapM_ (checkRulesInInstanceOrClass newClassEnv) instDecls
      mapM_ (checkRulesInInstanceOrClass newClassEnv) classDecls
      
      mapM_ (checkClassNameInInstance newClassEnv) instDecls
      
    -- ----------------------------------------------------------------------
    -- phase 3: checks that need the class environment, with
    --          qualified superclass/instance contexts 
    -- ----------------------------------------------------------------------
    phase3 = do  
      let newClasses' = 
            map (qualifyClass newClassEnv' . classDeclToClass m) 
                classDecls
          instances' =  
            map (qualifyInstance newClassEnv' . instanceDeclToInstance m tcEnv)
                instDecls 
            ++ importedInstances
          newClassEnv' = ClassEnv (bindAll newClasses' importedClasses) instances' emptyTopEnv
      
      mapM_ (checkForInstanceDataTypeExistAlsoInstancesForSuperclasses newClassEnv' tcEnv m) instDecls
      mapM_ (checkInstanceContextImpliesAllInstanceContextsOfSuperClasses newClassEnv' tcEnv m) instDecls
      
      checkForCyclesInClassHierarchy newClassEnv'
      
      checkForDuplicateInstances newClassEnv'
      
      return (newClasses', instances')
    -- |binds all classes into the given top environment
    -- (under the qualified as well as the unqualified name) 
    bindAll :: [Class] -> TopEnv Class -> TopEnv Class
    bindAll cls cEnv = foldr (\c env -> bindClass m env (unqualify $ theClass c) c) cEnv cls 

-- |converts a class declaration into the form of the class environment 
classDeclToClass :: ModuleIdent -> Decl -> Class
classDeclToClass m (ClassDecl _ (SContext scon) cls tyvar decls) 
  = Class { 
    superClasses = map fst scon, -- still unqualified!
    theClass = qualifyWith m cls, 
    typeVar = tyvar, 
    kind = -1, -- TODO
    methods = allMethods, 
    defaults = filter isFunctionDecl decls, 
    typeSchemes = []
  }
  where
    splitUpTypeSig :: Decl -> [Decl]
    splitUpTypeSig (TypeSig p ids cx ty) 
      = map (\id0 -> TypeSig p [id0] cx ty) ids
    splitUpTypeSig _ = internalError "splitUpTypeSig"
    allMethods = map (\(TypeSig _ [id0] cx ty) -> (id0, cx, ty)) $ 
      concatMap splitUpTypeSig $ filter isTypeSig decls
classDeclToClass _ _ = internalError "classDeclToClass"
  
-- |converts an instance declaration into the form of the class environment
instanceDeclToInstance :: ModuleIdent -> TCEnv -> Decl -> Instance
instanceDeclToInstance m tcEnv (InstanceDecl _ (SContext scon) cls tcon ids decls) = 
  Instance { 
    context = scon, -- still unqualified!
    iClass = cls,   -- still unqualified!
    iType = ty,     -- still unqualified!
    typeVars = ids, 
    rules = decls }
  where
  -- fromJust shouldn't fail here, because this function is first called
  -- after it has been checked that the given type exists
  ty = fromJust $ tyConToQualIdent m tcEnv tcon
instanceDeclToInstance _ _ _ = internalError "instanceDeclToInstance"

-- |Determines the qualified name for the given type constructor. This name 
-- refers always to the module where the given type constructor is defined, and
-- doesn't use the qualification in the source file (for example the qualification
-- used in connection with qualified module imports)
tyConToQualIdent :: ModuleIdent -> TCEnv -> TypeConstructor -> Maybe QualIdent
tyConToQualIdent m tcEnv (QualTC qid) = qualifyQid
  where
  qualifyQid = case qualLookupTC qid tcEnv of
    [DataType tc' _ _] -> Just tc'
    [RenamingType tc' _ _] -> Just tc'
    [AliasType _ _ _] -> Nothing
    _ -> case qualLookupTC (qualQualify m qid) tcEnv of
      [DataType tc' _ _] -> Just tc'
      [RenamingType tc' _ _] -> Just tc'
      [AliasType _ _ _] -> Nothing
      _ -> Nothing
tyConToQualIdent _ _ UnitTC = Just qUnitIdP
tyConToQualIdent _ _ (TupleTC n) = Just $ qTupleIdP n 
tyConToQualIdent _ _ ListTC = Just qListIdP
tyConToQualIdent _ _ ArrowTC = Just qArrowId

-- |qualifies superclasses in the class context
qualifyClass :: ClassEnv -> Class -> Class
qualifyClass cEnv cls = 
  cls { superClasses = 
    map (getCanonClassName cEnv)
        (superClasses cls) } 

-- |canonicalizes the class name: unqualified class names are qualified
-- with the module where the class is defined
getCanonClassName :: ClassEnv -> QualIdent -> QualIdent
getCanonClassName cEnv cls = theClass $ fromJust $ lookupClass cEnv cls

-- |qualifies superclasses in the instance context and the class in the instance
-- declaration
qualifyInstance :: ClassEnv -> Instance -> Instance
qualifyInstance cEnv i = 
  i { context = map (\(qid, id0) -> (getCanonClassName cEnv qid, id0)) (context i)
    , iClass = getCanonClassName cEnv (iClass i) }   

-- ----------------------------------------------------------------------------
-- functions for gathering/transforming type signatures
-- ----------------------------------------------------------------------------

-- |gathers *all* type signatures, also those that are in nested scopes and in
-- classes etc.
gatherTypeSigs :: [Decl] -> [Decl]
gatherTypeSigs decls = 
  -- filter isTypeSig decls ++ 
  concatMap gatherTS decls

gatherTS :: Decl -> [Decl]
gatherTS (ClassDecl _ _ _ _ decls) = gatherTypeSigs decls
gatherTS (InstanceDecl _ _ _ _ _ decls) = gatherTypeSigs decls
gatherTS (PatternDecl _ _ _ _ rhs) = gatherTSRhs rhs
gatherTS (FunctionDecl _ _ _ _ eqs) = concatMap gatherTSEqu eqs 
gatherTS ts@(TypeSig _ _ _ _) = [ts]
gatherTS _ = []

gatherTSRhs :: Rhs -> [Decl]
gatherTSRhs (SimpleRhs _ expr decls) = gatherTSExpr expr ++ gatherTypeSigs decls
gatherTSRhs (GuardedRhs cexps decls) = concatMap gatherTSCondExpr cexps ++ gatherTypeSigs decls

gatherTSEqu :: Equation -> [Decl]
gatherTSEqu (Equation _ _ rhs) = gatherTSRhs rhs

gatherTSExpr :: Expression -> [Decl]
gatherTSExpr (Literal _) = []
gatherTSExpr (Variable _ _) = []
gatherTSExpr (Constructor _) = []
gatherTSExpr (Paren expr) = gatherTSExpr expr
-- convert typification into type signatures without position (TODO: add
-- position somehow)
gatherTSExpr (Typed _ expr cx texp) = gatherTSExpr expr ++ [typeSig [] cx texp]
gatherTSExpr (Tuple _ exps) = concatMap gatherTSExpr exps
gatherTSExpr (List _ exps) = concatMap gatherTSExpr exps
gatherTSExpr (ListCompr _ expr stms) = gatherTSExpr expr ++ concatMap gatherTSStm stms
gatherTSExpr (EnumFrom expr) = gatherTSExpr expr
gatherTSExpr (EnumFromThen expr1 expr2) = gatherTSExpr expr1 ++ gatherTSExpr expr2
gatherTSExpr (EnumFromTo expr1 expr2) = gatherTSExpr expr1 ++ gatherTSExpr expr2
gatherTSExpr (EnumFromThenTo expr1 expr2 expr3) = 
  gatherTSExpr expr1 ++ gatherTSExpr expr2 ++ gatherTSExpr expr3
gatherTSExpr (UnaryMinus _ expr) = gatherTSExpr expr 
gatherTSExpr (Apply e1 e2) = gatherTSExpr e1 ++ gatherTSExpr e2
gatherTSExpr (InfixApply e1 _ e2) = gatherTSExpr e1 ++ gatherTSExpr e2
gatherTSExpr (LeftSection e _) = gatherTSExpr e
gatherTSExpr (RightSection _ e) = gatherTSExpr e
gatherTSExpr (Lambda _ _ e) = gatherTSExpr e
gatherTSExpr (Let decls expr) = gatherTypeSigs decls ++ gatherTSExpr expr
gatherTSExpr (Do stms e) = concatMap gatherTSStm stms ++ gatherTSExpr e
gatherTSExpr (IfThenElse _ e1 e2 e3) = 
  gatherTSExpr e1 ++ gatherTSExpr e2 ++ gatherTSExpr e3
gatherTSExpr (Case _ _ e alts) = gatherTSExpr e ++ concatMap gatherTSAlt alts
gatherTSExpr (RecordConstr fs) = concatMap gatherTSFieldExpr fs
gatherTSExpr (RecordSelection e _) = gatherTSExpr e
gatherTSExpr (RecordUpdate fs e) = concatMap gatherTSFieldExpr fs ++ gatherTSExpr e

gatherTSStm :: Statement -> [Decl]
gatherTSStm (StmtExpr _ e) = gatherTSExpr e
gatherTSStm (StmtDecl decls) = gatherTypeSigs decls
gatherTSStm (StmtBind _ _ e) = gatherTSExpr e

gatherTSCondExpr :: CondExpr -> [Decl]
gatherTSCondExpr (CondExpr _ e1 e2) = gatherTSExpr e1 ++ gatherTSExpr e2

gatherTSAlt :: Alt -> [Decl]
gatherTSAlt (Alt _ _ rhs) = gatherTSRhs rhs

gatherTSFieldExpr :: Field Expression -> [Decl]
gatherTSFieldExpr (Field _ _ e) = gatherTSExpr e

-- ---------------------------------------------------------------------------

-- |Translates the contexts in all type signatures by canonicalizing
-- all appearing class names (i.e., it replaces the given qualified class name
-- with a qualified class name in which the module identifier points to the
-- module where the class is actually defined)   
adjustContexts :: ClassEnv -> [Decl] -> [Decl]
adjustContexts cEnv ds = map (adjDecl cEnv) ds

adjDecl :: ClassEnv -> Decl -> Decl
adjDecl _    d@(InfixDecl _ _ _ _)   = d
adjDecl _    d@(DataDecl _ _ _ _)    = d
adjDecl _    d@(NewtypeDecl _ _ _ _) = d
adjDecl _    d@(TypeDecl _ _ _ _)    = d
adjDecl cEnv   (TypeSig p ids cx te) = TypeSig p ids (canonContext cEnv cx) te
adjDecl cEnv   (FunctionDecl p cty n f eqs) = 
  FunctionDecl p cty n f (map (adjEqu cEnv) eqs)
adjDecl _    d@(ForeignDecl _ _ _ _ _) = d
adjDecl _    d@(ExternalDecl _ _)      = d
adjDecl cEnv   (PatternDecl p cty n pt rhs) = PatternDecl p cty n pt (adjRhs cEnv rhs)
adjDecl _    d@(FreeDecl _ _) = d
adjDecl cEnv   (ClassDecl p scon cls v ds) = 
  ClassDecl p scon cls v (adjustContexts cEnv ds)
adjDecl cEnv   (InstanceDecl p scon cls ty vs ds) = 
  InstanceDecl p scon cls ty vs (adjustContexts cEnv ds)

adjEqu :: ClassEnv -> Equation -> Equation
adjEqu cEnv (Equation p lhs rhs) = Equation p lhs (adjRhs cEnv rhs)

adjRhs :: ClassEnv -> Rhs -> Rhs
adjRhs cEnv (SimpleRhs p e ds) = 
  SimpleRhs p (adjExpr cEnv e) (adjustContexts cEnv ds)
adjRhs cEnv (GuardedRhs ces ds) =
  GuardedRhs (map (adjCondExpr cEnv) ces) (adjustContexts cEnv ds)
 
adjCondExpr :: ClassEnv -> CondExpr -> CondExpr
adjCondExpr cEnv (CondExpr p e1 e2) = 
  CondExpr p (adjExpr cEnv e1) (adjExpr cEnv e2)

adjExpr :: ClassEnv -> Expression -> Expression
adjExpr _    e@(Literal _) = e
adjExpr _    e@(Variable _ _) = e
adjExpr _    e@(Constructor _) = e
adjExpr cEnv (Paren e) = Paren (adjExpr cEnv e)
adjExpr cEnv (Typed cty e cx ty) = 
  Typed cty (adjExpr cEnv e) (canonContext cEnv cx) ty
adjExpr cEnv (Tuple sref es) = Tuple sref (map (adjExpr cEnv) es)
adjExpr cEnv (List sref es) = List sref (map (adjExpr cEnv) es)
adjExpr cEnv (ListCompr sref e ss) = 
  ListCompr sref (adjExpr cEnv e) (map (adjStmt cEnv) ss)
adjExpr cEnv (EnumFrom e1) = EnumFrom (adjExpr cEnv e1)
adjExpr cEnv (EnumFromThen e1 e2) = EnumFromThen (adjExpr cEnv e1) (adjExpr cEnv e2)
adjExpr cEnv (EnumFromTo e1 e2) = EnumFromTo (adjExpr cEnv e1) (adjExpr cEnv e2)
adjExpr cEnv (EnumFromThenTo e1 e2 e3) = 
  EnumFromThenTo (adjExpr cEnv e1) (adjExpr cEnv e2) (adjExpr cEnv e3)
adjExpr cEnv (UnaryMinus i e) = UnaryMinus i (adjExpr cEnv e)
adjExpr cEnv (Apply e1 e2) = Apply (adjExpr cEnv e1) (adjExpr cEnv e2)
adjExpr cEnv (InfixApply e1 op e2) = InfixApply (adjExpr cEnv e1) op (adjExpr cEnv e2)
adjExpr cEnv (LeftSection e op) = LeftSection (adjExpr cEnv e) op
adjExpr cEnv (RightSection op e) = RightSection op (adjExpr cEnv e)
adjExpr cEnv (Lambda sref pts e) = Lambda sref pts (adjExpr cEnv e)
adjExpr cEnv (Let ds e) = Let (adjustContexts cEnv ds) (adjExpr cEnv e)
adjExpr cEnv (Do ss e) = Do (map (adjStmt cEnv) ss) (adjExpr cEnv e)
adjExpr cEnv (IfThenElse sref e1 e2 e3) = IfThenElse sref
  (adjExpr cEnv e1) (adjExpr cEnv e2) (adjExpr cEnv e3)
adjExpr cEnv (Case sref ct e alts) = 
  Case sref ct (adjExpr cEnv e) (map (adjAlt cEnv) alts)
adjExpr cEnv (RecordConstr fs) = RecordConstr (map (adjField cEnv) fs)
adjExpr cEnv (RecordSelection e i) = RecordSelection (adjExpr cEnv e) i
adjExpr cEnv (RecordUpdate fs e) = 
  RecordUpdate (map (adjField cEnv) fs) (adjExpr cEnv e)   

adjStmt :: ClassEnv -> Statement -> Statement
adjStmt cEnv (StmtExpr sref e) = StmtExpr sref (adjExpr cEnv e)
adjStmt cEnv (StmtDecl ds) = StmtDecl (adjustContexts cEnv ds)
adjStmt cEnv (StmtBind sref p e) = StmtBind sref p (adjExpr cEnv e)

adjAlt :: ClassEnv -> Alt -> Alt
adjAlt cEnv (Alt p pt rhs) = Alt p pt (adjRhs cEnv rhs)

adjField :: ClassEnv -> Field Expression -> Field Expression
adjField cEnv (Field p i e) = Field p i (adjExpr cEnv e)

-- |canonicalizes all classes in the given context: the given qualified class
-- name is replaced by the class name qualified with the module
-- where the class is in fact declared
canonContext :: ClassEnv -> Context -> Context
canonContext cEnv (Context cx) = 
  Context $ map 
    (\(ContextElem qid id0 tys) -> ContextElem (getCanonClassName cEnv qid) id0 tys) cx

-- ---------------------------------------------------------------------------
-- checks
-- ---------------------------------------------------------------------------

-- |check that in classes the type variables in the context are exactly the
-- one that is given after the class name
-- legal: Eq a => Ord a
-- illegal: Eq b => Ord a  
typeVariableInContext :: Decl -> Tcc ()
typeVariableInContext (ClassDecl p (SContext scon) _cls tyvar _decls) 
 = let idsInContext = map snd scon in 
   if not (null scon) && nub idsInContext /= [tyvar]
   then report (errTypeVariableInContext p (nub idsInContext \\ [tyvar]))
   else ok
typeVariableInContext _ = internalError "typeVariableInContext"

-- |check that the classes in superclass contexts or instance contexts are 
-- in scope and not ambiguous
checkClassesInContext :: ModuleIdent -> ClassEnv -> Decl -> Tcc ()
checkClassesInContext m cEnv (ClassDecl p (SContext scon) _ _ _) = 
  mapM_ (checkClassesInContext' m cEnv p) (map fst scon)
checkClassesInContext m cEnv (InstanceDecl p (SContext scon) _ _ _ _) = 
  mapM_ (checkClassesInContext' m cEnv p) (map fst scon)
checkClassesInContext m cEnv (TypeSig p _ (Context cx) _) = 
  mapM_ (checkClassesInContext' m cEnv p) (map (\(ContextElem qid _ _) -> qid) cx)
checkClassesInContext _ _ _ = internalError "TypeClassesCheck.checkClassesInContext"
    
checkClassesInContext' :: ModuleIdent -> ClassEnv -> Position -> QualIdent -> Tcc ()
checkClassesInContext' m cEnv p qid = 
  case lookupClass' cEnv (qualUnqualify m qid) of 
    []    -> report (errClassNotInScope p qid)
    [_]   -> ok
    (_:_) -> report (errAmbiguousClassName p qid) 

{-
lookupClassDecl :: [Decl] -> QualIdent -> Maybe Decl
lookupClassDecl (c@(ClassDecl _ _ cls _ _) : decls) cls' 
  | cls' == cls = Just c
  | otherwise   = lookupClassDecl decls cls'
lookupClassDecl [] _cls = Nothing
  -}

-- |check that there are no double class methods like in
-- class Foo1 a where fun :: a
-- class Foo2 a where fun :: a
-- TODO: improve position output
noDoubleClassMethods :: ModuleIdent -> [Decl] -> Tcc ()
noDoubleClassMethods m classDecls = 
  let allMethods = map fst3 $ concatMap (\(Class {methods=ms}) -> ms) classes
      theNub = nub allMethods -- nubBy (\ms1 ms2 -> fst3 ms1 == fst3 ms2) allMethods
  in if length theNub /= length allMethods
  then report (errDoubleClassMethods NoPos NoPos (allMethods \\ theNub))
  else ok
  where 
  classes = map (classDeclToClass m) classDecls

-- noConflictOfClassMethodsWithTopLevelBinding :: [Class] -> ValueEnv -> Tcc ()
-- noConflictOfClassMethodsWithTopLevelBinding = undefined

-- |check that the type variable of the class appears in all method type 
-- signatures. Example:
-- OK:
-- @
-- class C a where
--   fun1 :: a -> a
--   fun2 :: a -> b -> c -> d
-- @
-- Errors:
-- @ 
-- class C a where
--   fun3 :: b -> Int
--   fun4 :: Int
--   fun5 :: b -> c -> d -> Int
-- @
classMethodSigsContainTypeVar :: Decl -> Tcc ()
classMethodSigsContainTypeVar (ClassDecl _p _scon _tycon tyvar0 decls)
  = mapM_ (tyVarInTypeSig tyvar0) typeSigs
  where 
    typeSigs = filter isTypeSig decls
    tyVarInTypeSig tyvar (TypeSig p ids _con typeExpr) 
      = if tyvar `elem` typeVarsInTypeExpr typeExpr
        then ok
        else report (errTypeVarNotInMethodSig p tyvar ids)
    tyVarInTypeSig _ _ = internalError "TypeClassesCheck tyVarInTypeSig"
classMethodSigsContainTypeVar _ = internalError "TypeClassesCheck" 

-- |check that the rules in the instance declaration or default methods 
-- in a class declaration are for class methods only
-- Illegal:
-- class Eq a where fun1 :: a
-- instance Eq Int where fun2 = 1 -- fun2 is not a class method!
-- Illegal:
-- class Eq a where fun1 :: a -> a; fun2 = id 
checkRulesInInstanceOrClass :: ClassEnv -> Decl -> Tcc ()
checkRulesInInstanceOrClass cEnv decl = 
  mapM_ isDefinedFunctionClassMethod (getDecls decl)
  where 
    isDefinedFunctionClassMethod (cls, FunctionDecl p _ _ f _) 
      = let ms = maybe [] methods (lookupClass cEnv cls)
            eq = (\(id0, _, _) -> id0 == f)
        in 
        case find eq ms of
          Nothing -> report (errFunctionNoClassMethod p f)
          Just _ -> ok
    isDefinedFunctionClassMethod (_, TypeSig _ _ _ _) = ok
    isDefinedFunctionClassMethod _ = internalError "isDefinedFunctionClassMethod"

getDecls :: Decl -> [(QualIdent, Decl)]
getDecls (InstanceDecl _ _ cls _ _ decls) = zip (repeat cls) decls
getDecls (ClassDecl _ _ cls _ decls) = zip (repeat $ qualify cls) decls
getDecls _ = internalError "getDecls"

-- |Checks that there are no cycles in the class hierarchy. 
-- This can be determined by computing the strong connection components
-- and checking that each has only one element
checkForCyclesInClassHierarchy :: ClassEnv -> Tcc ()
checkForCyclesInClassHierarchy cEnv@(ClassEnv classes _ _) = 
  if all (==1) (map length sccs)
  then ok
  else mapM_ (report . errCyclesInClassHierarchy) (filter (\xs -> length xs > 1) sccs)
  where 
    sccs = scc (\qid -> [qid]) 
               (\qid -> (superClasses $ fromJust $ lookupClass cEnv qid))
               (map theClass (allClasses classes))

-- |Checks that in the superclass context the class declared doesn't appear
-- in the context (this is a special case of the "no cycles" check which 
-- doesn't cover this case):
-- @class A a => A a where ...@ is illegal 
-- Theoretically one could write this --- but who does? But well, we have
-- nevertheless to cover this case...
checkForDirectCycle :: ModuleIdent -> Decl -> Tcc ()
checkForDirectCycle m (ClassDecl _ (SContext cx) cls _ _) = 
  if (qualify cls) `elem` (map fst cx) || (qualifyWith m cls) `elem` (map fst cx)
  then report (errCyclesInClassHierarchy [qualify cls])
  else ok
checkForDirectCycle _ _ = internalError "checkForDirectCycle"

-- |Checks for duplicate class names like in 
-- @
-- class A a
-- class A a
-- @
checkForDuplicateClassNames :: [Decl] -> Tcc ()
checkForDuplicateClassNames classes = 
  let duplClassNames = findMultiples $ map idFromCls classes
  in if null duplClassNames
  then ok
  else report (errDuplicateClassNames (map head duplClassNames))
  where
  idFromCls (ClassDecl _ _ cls _ _) = cls
  idFromCls _ = internalError "checkForDuplicateClassNames"


-- |Checks that there is at most one instance for a given class and type
checkForDuplicateInstances :: ClassEnv -> Tcc ()
checkForDuplicateInstances (ClassEnv _classes instances _) 
  = let duplInstances 
          = findMultiples $ map (\i -> (iClass i, iType i)) instances
    in if null duplInstances
    then ok
    else report (errDuplicateInstances (map head duplInstances))


-- |Check that in an instance definition type variables don't appear twice like
-- in @instance C (T a a)@
instanceTypeVarsDoNotAppearTwice :: Decl -> Tcc ()
instanceTypeVarsDoNotAppearTwice (InstanceDecl p _scon cls tcon ids _) 
  = let duplTypeVars = findMultiples ids
    in if null duplTypeVars then ok
    else report (errDuplicateTypeVars p cls tcon (map head duplTypeVars))
instanceTypeVarsDoNotAppearTwice _ = internalError "instanceTypeVarsDoNotAppearTwice"

-- |Checks that the class name in an instance definition is in scope
-- and that it is not ambiguous
checkClassNameInInstance :: ClassEnv -> Decl -> Tcc ()
checkClassNameInInstance cEnv (InstanceDecl p _ cls _ _ _) = 
  case lookupClass' cEnv cls of
    []    -> report (errClassNameNotInScope p cls)
    [_]   -> ok
    (_:_) -> report (errAmbiguousClassName p cls)
checkClassNameInInstance _ _ = internalError "checkClassNameInScope"

-- |Checks whether the instance data type is in scope and not a type synonym. 
-- Check also that the arity of the data type in the instance declaration
-- is correct. 
checkInstanceDataTypeCorrect :: TCEnv -> Decl -> Tcc ()
checkInstanceDataTypeCorrect tcEnv (InstanceDecl p _ _ (QualTC qid) ids _) =
  if length tinfo > 1
  then report (errDataTypeAmbiguous p qid)
  else if null tinfo
  then report (errDataTypeNotInScope p qid)
  else do
    when (isAliasType $ head tinfo) $ report (errTypeInInstanceDecl p qid)
    when (tcArity (head tinfo) /= length ids) $ report (errDataTypeHasIncorrectArity p qid)  

  where tinfo = qualLookupTC qid tcEnv 
        isAliasType (AliasType _ _ _) = True
        isAliasType _ = False

checkInstanceDataTypeCorrect _ (InstanceDecl p _ _ UnitTC ids _) = 
  unless (null ids) $ report (errDataTypeHasIncorrectArity p qUnitId)
checkInstanceDataTypeCorrect _ (InstanceDecl p _ _ (TupleTC n) ids _) =
  unless (length ids == n) $ report (errDataTypeHasIncorrectArity p (qTupleId n))
checkInstanceDataTypeCorrect _ (InstanceDecl p _ _ ListTC ids _) =
  unless (length ids == 1) $ report (errDataTypeHasIncorrectArity p qListId)
checkInstanceDataTypeCorrect _ (InstanceDecl p _ _ ArrowTC ids _) =
  unless (length ids == 2) $ report (errDataTypeHasIncorrectArity p qArrowId)  
checkInstanceDataTypeCorrect _ _ = internalError "checkInstanceDataTypeCorrect"

-- |Checks that there are only type vars in the context that also appear on
-- the right side
checkTypeVarsInContext :: Decl -> Tcc ()
checkTypeVarsInContext (TypeSig p _ids cx tyexp) = 
  case null wrongVars of
    True -> ok
    False -> report (errContextVariableNotOnTheRightSide p wrongVars "type signature")
  -- TODO: check that all context elements are in head normal form
  where
    varsInTypeExp = nub $ typeVarsInTypeExpr tyexp
    varsInContext = nub $ typeVarsInContext cx
    wrongVars = varsInContext \\ varsInTypeExp
checkTypeVarsInContext (InstanceDecl p scx _qid _ ids _decls) = 
  case null wrongVars of
    True -> ok
    False -> report (errContextVariableNotOnTheRightSide p wrongVars "instance declaration")
  where
    varsInTypeExp = nub $ ids
    varsInContext = nub $ typeVarsInSContext scx
    wrongVars = varsInContext \\ varsInTypeExp
checkTypeVarsInContext _ = internalError "typeSigCorrect"

-- |Assuming we have an instance `instance C (T ...)`, we must verify that
-- for each superclass S of C there is also an instance declaration 
-- `instance S (T ...)`
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses :: 
    ClassEnv -> TCEnv -> ModuleIdent -> Decl -> Tcc ()
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses cEnv tcEnv m
    (InstanceDecl p _scon cls ty _tyvars _)
  = let -- TODO: is it sufficient to take only direct superclasses? 
        -- scs = superClasses (fromJust $ lookupClass cEnv cls)
        scs = allSuperClasses cEnv cls
        tyId = tyConToQualIdent m tcEnv ty
        insts = map (\c -> getInstance cEnv c (fromJust tyId)) scs 
        missingInsts = map fst $ filter (isNothing . snd) $ zip scs insts in
    when (isJust tyId) $ unless (all isJust insts) $ report $ 
      errMissingSuperClassInstances p ty missingInsts      
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses _ _ _ _
  = internalError "checkForInstanceDataTypeExistAlsoInstancesForSuperclasses"
  

-- |Returns a Base.Types.Context for the given instance declaration. The type
-- variables are numbered beginning with zero. 
getContextFromInstDecl :: Decl -> BTC.Context
getContextFromInstDecl (InstanceDecl _p (SContext scon) _cls _ty tyvars _)
  = getContextFromSContext scon tyvars
getContextFromInstDecl _ = internalError "getContextFromInst"

-- |Returns a Base.Types.Context for the given instance. The type
-- variables are numbered beginning with zero. 
getContextFromInst :: Instance -> BTC.Context
getContextFromInst i = getContextFromSContext (context i) (typeVars i)

-- |Converts an SContext to a Base.Types.Context, considering the given
-- type variables from the instance declaration. 
getContextFromSContext :: [(QualIdent, Ident)] -> [Ident] -> BTC.Context
getContextFromSContext scon tyvars = 
  let mapping = zip tyvars [0::Int ..] in
  map (\(qid, id0) -> (qid, TypeVariable $ fromJust $ lookup id0 mapping)) scon

-- |Converts a Base.Types.Context back into a simple context, considering the
-- given type variables. 
getSContextFromContext :: BTC.Context -> [Ident] -> [(QualIdent, Ident)]
getSContextFromContext con tyvars = 
  let mapping = zip [0::Int ..] tyvars in
  map (\(qid, TypeVariable n) -> (qid, fromJust $ lookup n mapping)) con

-- |Checks that for a given instance declaration `instance cx => C (T ...)` 
-- the context cx implies *all* contexts of instance declarations for 
-- the same type and the superclasses of C
checkInstanceContextImpliesAllInstanceContextsOfSuperClasses :: 
    ClassEnv -> TCEnv -> ModuleIdent -> Decl -> Tcc ()
checkInstanceContextImpliesAllInstanceContextsOfSuperClasses cEnv tcEnv m
    inst@(InstanceDecl p _scon cls ty tyvars _)
  = let thisContext = getContextFromInstDecl inst
        scs = allSuperClasses cEnv cls
        tyId = tyConToQualIdent m tcEnv ty
        insts = map fromJust $ filter isJust $ 
          map (\c -> getInstance cEnv c (fromJust tyId)) scs
        instCxs = concatMap getContextFromInst insts
        
        thisContext' = getSContextFromContext thisContext tyvars
        instCxs' = getSContextFromContext instCxs tyvars
        notImplCxs = (filter (not . implies cEnv thisContext) instCxs)
        notImplCxs' = getSContextFromContext notImplCxs tyvars in
    when (isJust tyId) $ unless (implies' cEnv thisContext instCxs) $ report $  
      errContextNotImplied p thisContext' instCxs' notImplCxs'
        
checkInstanceContextImpliesAllInstanceContextsOfSuperClasses _ _ _ _
  = internalError "checkInstanceContextImpliesAllInstanceContextsOfSuperClasses"

-- | Check that in the type signatures of the class only the type variable
-- of the class is used. TODO: later allow this! 
checkCorrectTypeVarsInTypeSigs :: Decl -> Tcc ()
checkCorrectTypeVarsInTypeSigs (ClassDecl _ _ _ tyvar ds) = do
  mapM_ checkTypeVars tyVarsSigs
  where
  tySigs = filter isTypeSig ds
  tyVarsSigs = map tyVars tySigs
  tyVars (TypeSig p _ _ te) = (p, typeVarsInTypeExpr te)
  tyVars _ = internalError "checkTypeVarsInTypeSigs"
  checkTypeVars (p, tyvars) = 
    when (nub tyvars /= [tyvar]) $ 
      report $ errNotAllowedTypeVars p (nub tyvars \\ [tyvar])
checkCorrectTypeVarsInTypeSigs _ = internalError "checkCorrectTypeVarsInTypeSigs"
  


-- ---------------------------------------------------------------------------
-- source code transformation
-- ---------------------------------------------------------------------------

-- |Transforms class declarations by generating a special data type for 
-- the dictionaries. Disadvantage: Only class methods possible that do not contain
-- other type variables than the type variable given in the class declaration. 
-- Things like
-- @
-- class A a where
--   fun :: a -> b
-- @
-- are therefore not allowed.  
transformClass :: ClassEnv -> Decl -> [Decl]
transformClass cEnv (ClassDecl _p _scx cls tyvar _decls) = 
  [ DataDecl NoPos dataTypeName typeVars0 [
     ConstrDecl NoPos existTypeVars dataTypeName (scs ++ methodTypes) ]
  ] ++ concatMap genSuperClassDictSelMethod theSuperClasses 
    ++ concatMap genMethodSelMethod (zip theMethods0 [0..])
  where
  theClass0 = fromJust $ lookupClass cEnv (qualify cls)
  theMethods0 = methods theClass0
  -- existTypeVars = (nub $ concatMap (typeVarsInTypeExpr . third) theMethods0) \\ [tyvar]
  existTypeVars = []
  typeVars0 = [tyvar]
  third (_, _, x) = x
  dataTypeName = mkIdent $ dictTypePrefix ++ show cls
  theSuperClasses = map show $ superClasses theClass0
  qSuperClasses = map (dictTypePrefix ++) theSuperClasses
  scs = map (\s -> ConstructorType (mkQIdent s) [VariableType tyvar])
    qSuperClasses
  methodTypes = map third theMethods0
  genSuperClassDictSelMethod :: String -> [Decl]
  genSuperClassDictSelMethod scls = 
    let selMethodId = mkIdent $ selMethodName
        selMethodName = mkSelFunName (show $ theClass theClass0) scls in
    [ typeSig [selMethodId]
        emptyContext (ArrowType 
          (ConstructorType (qualify $ dataTypeName) [VariableType tyvar]) 
          (ConstructorType (mkQIdent $ dictTypePrefix ++ scls) [VariableType tyvar]))
    , fun selMethodId 
       [equation
         (equationsLhs selMethodName)
         (simpleRhs (qVar $ dictSelParam selMethodName scls))
       ]
    ]
  genMethodSelMethod :: ((Ident, Context, TypeExpr), Int) -> [Decl]
  genMethodSelMethod ((m, _cx, ty), i) = 
    let selMethodId = mkIdent $ selMethodName
        selMethodName = mkSelFunName (show $ theClass theClass0) (show m) in
    [ typeSig [selMethodId]
        emptyContext (ArrowType 
          (ConstructorType (mkQIdent $ dictTypePrefix ++ (show cls)) [VariableType tyvar]) 
          ty)
    , fun selMethodId 
       [equation
         (equationsLhs selMethodName)
         (simpleRhs (qVar $ methodSelParam selMethodName i))
       ]
    ]
  equationsLhs selMethodName = let selMethodId = mkIdent $ selMethodName in 
    FunLhs selMethodId [ConstructorPattern (qualify $ dataTypeName) 
      (map (\s -> VariablePattern $ dictSelParam selMethodName s) theSuperClasses
       ++ map (\(n, _) -> VariablePattern $ methodSelParam selMethodName n)
         (zip [0::Int ..] theMethods0))]
  
  -- the renamings are important so that the parameters are not handled as
  -- global functions    
  dictSelParam selMethodName s = flip renameIdent 1 $ 
    mkIdent (identPrefix ++ selMethodName ++ sep ++ s)
  methodSelParam selMethodName n = flip renameIdent 1 $ 
    mkIdent (identPrefix ++ selMethodName ++ sep ++ "x" ++ (show n))
  
transformClass _ d = [d]


-- |Transforms class declarations using tuples as dictionaries. This handles
-- class methods with other type variables than the type variable given in the class
-- declaration well (?)
transformClass2 :: ClassEnv -> Decl -> [Decl]
transformClass2 cEnv (ClassDecl _p _scx cls _tyvar _decls) = 
  concatMap genSuperClassDictSelMethod superClasses0
  ++ concatMap genMethodSelMethod (zip methods0 [0..])
  ++ concatMap genNonDirectSuperClassDictSelMethod nonDirectSuperClasses
  where
  theClass0 = fromJust $ lookupClass cEnv (qualify cls)
  superClasses0 = map show $ superClasses theClass0
  superClasses1 = superClasses theClass0
  methods0 = methods theClass0
  nonDirectSuperClasses = allSuperClasses cEnv (theClass theClass0) \\ superClasses1
  
  -- | Generates functions for extracting (direct) super class dictionaries 
  -- from a given dictionary
  genSuperClassDictSelMethod :: String -> [Decl]
  genSuperClassDictSelMethod scls = 
    let selMethodName = mkSelFunName (show $ theClass theClass0) scls in
    [ fun (mkIdent selMethodName)
      [equation
        (equationLhs selMethodName)
        (simpleRhs (qVar $ dictSelParam selMethodName scls))
      ]
    ]
    
  -- | Generates functions for extracting the class functions from a given 
  -- directory 
  genMethodSelMethod :: ((Ident, Context, TypeExpr), Int) -> [Decl]
  genMethodSelMethod ((m, _cx, _ty), i) = 
    let selMethodName = mkSelFunName (show $ theClass theClass0) (show m) in
    [ fun (mkIdent selMethodName)
      [equation
        (equationLhs selMethodName)
        (simpleRhs (qVar $ methodSelParam selMethodName i))
      ]
    ]
  
  -- | The left side of the (direct) selection functions is always the same and
  -- created by this function  
  equationLhs selMethodName = 
    FunLhs (mkIdent selMethodName) [
      if length patterns > 1 then TuplePattern noRef patterns
      else if length patterns == 1 then head patterns
      else internalError "transformClass2"]
    where
    patterns = (
      map (\s -> VariablePattern $ dictSelParam selMethodName s) superClasses0
      ++ map (\(n, _) -> VariablePattern $ methodSelParam selMethodName n)
        (zip [0::Int ..] methods0))
  
  -- | generate selector function for a non-direct superclass of the given 
  -- class. If for example the superclass hierarchy is A -> B -> C -> D, then 
  -- among others the following selector functions are created:
  -- @ 
  -- sel.D.A = sel.B.A . sel.C.B . sel.D.C
  -- sel.C.A = sel.B.A . sel.C.B
  -- @
  genNonDirectSuperClassDictSelMethod :: QualIdent -> [Decl]
  genNonDirectSuperClassDictSelMethod scls = 
    let selMethodName = mkSelFunName (show $ theClass theClass0) (show scls) in
    [ fun (mkIdent selMethodName)
      [equation
        (FunLhs (mkIdent selMethodName) [])
        (simpleRhs expr)
      ]
    ]
    where
    -- we want the shortest path in the superclass hierarchy to the given 
    -- superclass
    path = fromJust $ findPath cEnv (theClass theClass0) scls 
    -- generate the names of the selector functions 
    names :: [QualIdent] -> [Expression]
    names (x:y:zs) = 
      (qVar $ mkIdent $ mkSelFunName (show x) (show y)) 
      : names (y:zs)
    names [_] = []
    names [] = internalError "genNonDirectSuperClassDictSelMethod"
    -- enchain the selector functions
    expr :: Expression
    expr = foldr1 (\e1 e2 -> InfixApply e1 (InfixOp Nothing point) e2) (reverse $ names path)
    point = mkQIdent "."
    
  -- the renamings are important so that the parameters are not handled as
  -- global functions. Also important is that the parameters are globally
  -- unique
  dictSelParam selMethodName s = flip renameIdent 1 $ 
    mkIdent (identPrefix ++ selMethodName ++ sep ++ s)
  methodSelParam selMethodName n = flip renameIdent 1 $ 
    mkIdent (identPrefix ++ selMethodName ++ sep ++ "x" ++ (show n))
  
  
transformClass2 _ d = [d]

type IDecl = Decl

-- |transformInstance creates top level functions for the methods 
-- of which rules are given in the instance declaration, and concrete 
-- dictionaries, as well as type signatures for the instance rules. 
transformInstance :: ModuleIdent -> ClassEnv -> TCEnv -> IDecl -> [Decl]
transformInstance m cEnv tcEnv idecl@(InstanceDecl _ _ cls tycon _ decls)
  = concatMap (transformMethod cEnv idecl ity) decls
  ++ concatMap (handleMissingFunc cEnv idecl ity) missingMethods
  -- create dictionary 
  ++ createDictionary2 cEnv idecl ity
  where
  ity = fromJust $ tyConToQualIdent m tcEnv tycon
  presentMethods = nub $ map (\(FunctionDecl _ _ _ id0 _) -> id0) decls
  theClass0 = fromJust $ lookupClass cEnv cls 
  theMethods0 = nub $ map fst3 $ methods theClass0
  missingMethods = theMethods0 \\ presentMethods
transformInstance _ _ _ d = [d]

-- |transforms one method defined in an instance to a top level function 
transformMethod :: ClassEnv -> IDecl -> QualIdent -> Decl -> [Decl]
transformMethod cEnv idecl@(InstanceDecl _ _ cls _ _ _) ity
                     decl@(FunctionDecl _ _ _ _ _) =
  -- create type signature
  createTypeSignature rfunc cEnv idecl decl
  -- create function rules
  : [createTopLevelFuncs cEnv rfunc idecl decl] 
  where 
    cls' = getCanonClassName cEnv cls
    -- rename for specific instance!
    rfunc = (\s -> instMethodName cls' ity s)
transformMethod _ _ _ _ = internalError "transformMethod"

-- |create a name for the (hidden) function that is implemented by the  
-- function definitions in the instance  
instMethodName :: QualIdent -> QualIdent -> String -> String
instMethodName cls tcon s = implPrefix ++ show cls ++ sep ++ show tcon ++ sep ++ s

-- |creates a type signature for an instance method which is transformed to
-- a top level function
createTypeSignature :: RenameFunc -> ClassEnv -> IDecl -> Decl -> Decl
createTypeSignature rfunc cEnv (InstanceDecl _ scx cls tcon tyvars _) 
                    (FunctionDecl p _ _ f _eqs) 
  = TypeSig p [rename rfunc f] cx' ty''
  where
    (cx, ty) = fromJust $ lookupMethodTypeSig' cEnv cls f 
    theClass_ = fromJust $ lookupClass cEnv cls
     
    -- Substitute class typevar with given instance type. 
    -- Rename tyvars, so that they do not equal type vars in the class
    -- method type signature, like in the following example:
    -- class C a where fun :: a -> b -> Bool
    -- instance Eq b => C (S b) where fun = ...
    theType = SpecialConstructorType tcon (map (VariableType . flip renameIdent 1) tyvars)
    
    subst = [(typeVar theClass_, theType)]
    -- cx' = substInContext subst cx
    ty' = substInTypeExpr subst ty
    ty'' = if arrowArity ty' == 0 then ArrowType (TupleType []) ty' else ty'
    
    -- add instance context. The variables have to be renamed here as well
    renamedSContext = (\(SContext elems) -> 
      SContext $ map (\(qid, id0) -> (qid, renameIdent id0 1)) elems) scx
    icx = simpleContextToContext renamedSContext
    cx' = combineContexts icx cx
createTypeSignature _ _ _ _ = internalError "createTypeSignature"    

combineContexts :: ST.Context -> ST.Context -> ST.Context
combineContexts (Context e1) (Context e2) = Context (e1 ++ e2)

type RenameFunc = String -> String

-- |All concrete implementations of class methods in an instance declaration are
-- shifted by this function to top level, using new generated function names
-- for the definitions. 
createTopLevelFuncs :: ClassEnv -> RenameFunc -> IDecl -> Decl -> Decl
createTopLevelFuncs cEnv rfunc (InstanceDecl _ _ cls _ _ _) 
                               (FunctionDecl p cty n id0 eqs) 
  = FunctionDecl p cty n (rename rfunc id0) (map (transEqu zeroArity rfunc) eqs)
  where
  (_, ty) = fromJust $ lookupMethodTypeSig' cEnv cls id0
  zeroArity = arrowArity ty == 0
createTopLevelFuncs _ _ _ _ = internalError "createTopLevelFuncs"

-- |As we create top-level functions, all occurences of the prior function
-- name must be replaced with the new top-level function name. Therefore, in 
-- the left hand sides of the equations, the function names have to be updated.
transEqu :: Bool -> RenameFunc -> Equation -> Equation
transEqu zeroArity rfunc (Equation p lhs rhs) = 
  Equation p (transLhs zeroArity rfunc lhs) rhs

-- |Renames the given function names with the new top level function names. 
-- Also adds an additional unit argument for implementations of nullary class
-- methods. 
transLhs :: Bool -> RenameFunc -> Lhs -> Lhs
-- TODO: throw internal error when illegal combination is found?
-- transLhs False rfunc (FunLhs id0 ps@(_:_)) = FunLhs (rename rfunc id0) ps
-- transLhs True rfunc (FunLhs id0 []) = FunLhs (rename rfunc id0) [TuplePattern noRef []]
-- transLhs False rfunc (OpLhs ps1 id0 ps2) = OpLhs ps1 (rename rfunc id0) ps2
-- transLhs True _ (OpLhs _ _ _) = internalError "transLhs: zero arity with operator lhs"
transLhs zeroArity rfunc (FunLhs id0 ps) = 
  FunLhs (rename rfunc id0) (if zeroArity then TuplePattern noRef [] : ps else ps)
transLhs _ rfunc (OpLhs ps1 id0 ps2) = OpLhs ps1 (rename rfunc id0) ps2
transLhs zeroArity rfunc (ApLhs lhs ps) = ApLhs (transLhs zeroArity rfunc lhs) ps

rename :: RenameFunc -> Ident -> Ident
rename rfunc = updIdentName rfunc  

-- |calculates the arity of a given type signature
arrowArity :: TypeExpr -> Int
arrowArity (ArrowType _ ty) = 1 + arrowArity ty
arrowArity (SpecialConstructorType ArrowTC [_, ty]) = 1 + arrowArity ty
arrowArity _                = 0

-- |handles functions missing in an instance declaration. Searches for a
-- default method (TODO!) and inserts this, else inserts an error statement
handleMissingFunc :: ClassEnv -> IDecl -> QualIdent -> Ident -> [Decl]
handleMissingFunc cEnv (InstanceDecl _ _ cls _tcon _ _) ity fun0 = 
  [ fun globalName [if defaultMethodDefined then equ2 else equ1]
  ]
  where
  cls' = getCanonClassName cEnv cls
  globalName = mkIdent $ instMethodName cls' ity (show fun0)
  equ1 = equation (FunLhs globalName []) 
    (simpleRhs (Apply (qVar . mkIdent $ "error") 
                      (Literal $ String (srcRef 0) errorString)))
  errorString = show fun0 ++ " not given in instance declaration of class "
    ++ show cls' ++ " and type " ++ show ity
  equ2 = undefined -- TODO
  defaultMethodDefined = False -- TODO
handleMissingFunc _ _ _ _ = internalError "handleMissingFunc"

-- |This function creates a dictionary for the given instance declaration, 
-- using dictionary data types instead of tuples
createDictionary :: ClassEnv -> IDecl -> QualIdent -> [Decl]
createDictionary cEnv (InstanceDecl _ _scx cls0 _ _tvars _decls) ity = 
  [ fun (dictName cls)
    [equation
      (FunLhs (dictName cls) [])
      (simpleRhs all')
      ]
  ] 
  where
  cls = getCanonClassName cEnv cls0
  dictName c = mkIdent $ mkDictName (show c) (show ity)
  theClass0 = fromJust $ lookupClass cEnv cls0
  superClasses0 = superClasses theClass0
  methods0 = methods theClass0
  scs = map (qVar . dictName) superClasses0
  ms = map (qVar . mkIdent . 
    (\s -> instMethodName cls ity s) . show . fst3) methods0
  all0 = scs ++ ms
  dict = mkQIdent $ dictTypePrefix ++ show cls
  all' = foldl Apply (Constructor dict) all0
createDictionary _ _ _ = internalError "createDictionary"

-- |This function creates a dictionary for the given instance declaration, 
-- using tuples
createDictionary2 :: ClassEnv -> IDecl -> QualIdent -> [Decl]
createDictionary2 cEnv (InstanceDecl _ _scx cls0 _tcon _tvars _decls) ity = 
  [ fun (dictName cls)
    [equation
      (FunLhs (dictName cls) [])
      (simpleRhs 
        (if length all0 == 1 then head all0 else Tuple noRef all0))
      ]
  ] 
  where
  cls = getCanonClassName cEnv cls0
  dictName c = mkIdent $ mkDictName (show c) (show ity)
  theClass0 = fromJust $ lookupClass cEnv cls0
  superClasses0 = superClasses theClass0
  methods0 = methods theClass0
  scs = map (qVar . dictName) superClasses0
  ms = map (qVar . mkIdent . 
    (\s -> instMethodName cls ity s) . show . fst3) methods0
  all0 = scs ++ ms
createDictionary2 _ _ _ = internalError "createDictionary"

-- ---------------------------------------------------------------------------
-- helper functions
-- ---------------------------------------------------------------------------

qVar :: Ident -> Expression
qVar = Variable Nothing . qualify 

mkQIdent :: String -> QualIdent
mkQIdent = qualify . mkIdent

fun :: Ident -> [Equation] -> Decl
fun = FunctionDecl NoPos Nothing (-1)

equation :: Lhs -> Rhs -> Equation
equation = Equation NoPos

typeSig :: [Ident] -> Context -> TypeExpr -> Decl
typeSig = TypeSig NoPos

simpleRhs :: Expression -> Rhs
simpleRhs e = SimpleRhs NoPos e []

-- ---------------------------------------------------------------------------
-- other transformations
-- ---------------------------------------------------------------------------

-- |the variables in class method type signatures have to be renamed, so that
-- in the following example the type variable b in the first method declaration 
-- does not refer to the type variable b in the second method declaration:
-- class F a where
--   fun1 :: a -> b -> a
--   fun2 :: b -> a -> a 
renameTypeSigVars :: Class -> Class
renameTypeSigVars cls 
  = cls { methods = renameTypeSigVars' (typeVar cls) (methods cls) 1 }
  where
    renameTypeSigVars' :: Ident -> [(Ident, ST.Context, TypeExpr)] 
                      -> Int -> [(Ident, ST.Context, TypeExpr)]  
    renameTypeSigVars' _classTyvar [] _n = []
    renameTypeSigVars' classTyvar ((id0, cx, tyExp) : ms) n 
      = let allTypeVars = typeVarsInTypeExpr tyExp
            subst = buildSubst classTyvar allTypeVars n
        in (id0, renameVarsInContext subst cx, renameVarsInTypeExpr subst tyExp)
         : renameTypeSigVars' classTyvar ms (n+1)

buildSubst :: Ident -> [Ident] -> Int -> (Subst Ident)
buildSubst classTyvar ids n = map 
  (\id0 -> if id0 == classTyvar then (id0, id0)
           else (id0, updIdentName (\i -> i ++ show n) id0))
  ids

-- ---------------------------------------------------------------------------

-- |translates the methods to type schemes. The type variable of the class
-- has always the index 0!
buildTypeSchemes :: ModuleIdent -> TCEnv -> Class -> Class
buildTypeSchemes m tcEnv cls@(Class { theClass = tc, methods = ms, typeVar = classTypeVar }) 
  = cls { typeSchemes = map buildTypeScheme ms }
  where 
    buildTypeScheme :: (Ident, ST.Context, TypeExpr) -> (Ident, TypeScheme)
    buildTypeScheme (id0, (Context cElems), typeExpr) =
      -- add also the class to the context!
      let extendedCx = Context (ContextElem tc classTypeVar [] : cElems)
          (translatedContext, theType) = toConstrType [classTypeVar] (extendedCx, typeExpr) 
      in (id0, polyType (expandType m tcEnv theType) `constrainBy` translatedContext)



-- ---------------------------------------------------------------------------
-- various substitutions
-- ---------------------------------------------------------------------------

-- |The type for substitutions
type Subst a = [(Ident, a)]

applySubst :: (Subst Ident) -> Ident -> Ident
applySubst subst id0 = case lookup id0 subst of
  Nothing -> id0
  Just x -> x

-- | renames the type variables in the given context by using the given 
-- substitution
renameVarsInContext :: (Subst Ident) -> ST.Context -> ST.Context
renameVarsInContext subst (Context elems) = 
  Context $ map (renameVarsInContextElem subst) elems

renameVarsInContextElem :: (Subst Ident) -> ContextElem -> ContextElem
renameVarsInContextElem subst (ContextElem qid i texps)
  = ContextElem qid (applySubst subst i) (map (renameVarsInTypeExpr subst) texps)

renameVarsInTypeExpr :: (Subst Ident) -> TypeExpr -> TypeExpr
renameVarsInTypeExpr subst (ConstructorType qid texps) 
  = ConstructorType qid (map (renameVarsInTypeExpr subst) texps)
renameVarsInTypeExpr subst (SpecialConstructorType tcon texps) 
  = SpecialConstructorType tcon (map (renameVarsInTypeExpr subst) texps)
renameVarsInTypeExpr subst (VariableType id0) = VariableType $ applySubst subst id0
renameVarsInTypeExpr subst (TupleType texps) 
  = TupleType (map (renameVarsInTypeExpr subst) texps)
renameVarsInTypeExpr subst (ListType texp) = ListType $ renameVarsInTypeExpr subst texp
renameVarsInTypeExpr subst (ArrowType t1 t2) 
  = ArrowType (renameVarsInTypeExpr subst t1) (renameVarsInTypeExpr subst t2)
renameVarsInTypeExpr _subst (RecordType _ _) = internalError "TypeClassesCheck"

-- ---------------------------------------------------------------------------

applySubst' :: (Subst TypeExpr) -> Ident -> TypeExpr
applySubst' subst id0 = case lookup id0 subst of
  Nothing -> VariableType id0
  Just x -> x

-- |replaces the variables in the given type expression by type expressions, 
-- using the given substitution
substInTypeExpr :: (Subst TypeExpr) -> TypeExpr -> TypeExpr
substInTypeExpr subst (ConstructorType qid texps) 
  = ConstructorType qid (map (substInTypeExpr subst) texps)
substInTypeExpr subst (SpecialConstructorType tcon texps) 
  = SpecialConstructorType tcon (map (substInTypeExpr subst) texps)
substInTypeExpr subst (VariableType id0) = applySubst' subst id0
substInTypeExpr subst (TupleType texps) 
  = TupleType (map (substInTypeExpr subst) texps)
substInTypeExpr subst (ListType texp) = ListType $ substInTypeExpr subst texp
substInTypeExpr subst (ArrowType t1 t2) 
  = ArrowType (substInTypeExpr subst t1) (substInTypeExpr subst t2)
substInTypeExpr _subst (RecordType _ _) = internalError "TypeClassesCheck"

-- ---------------------------------------------------------------------------
-- error messages
-- ---------------------------------------------------------------------------

errTypeVariableInContext :: Position -> [Ident] -> Message
errTypeVariableInContext p ids 
  = posMessage p 
  (text "Illegal type variable(s)" <+> text (show ids) 
   <+> text "in class context")
  
errClassNotInScope :: Position -> QualIdent -> Message
errClassNotInScope p qid = 
  posMessage p (text "Class" <+> text (show qid)
  <+> text "not in scope") 
  
errDoubleClassMethods :: Position -> Position -> [Ident] -> Message
errDoubleClassMethods _p1 _p2 methods_ = 
  message (text "double class methods:" <+> text (show methods_) )

errTypeVarNotInMethodSig :: Position -> Ident -> [Ident] -> Message
errTypeVarNotInMethodSig p tyvar ids = 
  posMessage p (text "the type variable of the class definition" 
  <+> parens (ppIdent tyvar) 
  <+> text "not in method signature of" 
  <+> brackets (hsep $ punctuate comma (map ppIdent ids)))

errFunctionNoClassMethod :: Position -> Ident -> Message
errFunctionNoClassMethod p id0
  = posMessage p (text "the function" <+> text (escName id0) 
  <+> text "is not a class method! ") 
  
errCyclesInClassHierarchy :: [QualIdent] -> Message
errCyclesInClassHierarchy qids
  = message (text "There are cycles in the class hierarchy. Classes concerned: "
  <+> hsep (punctuate comma (map ppQIdent qids)))

errDuplicateClassNames :: [Ident] -> Message
errDuplicateClassNames clss 
  = message (text "Two or more classes with the same name: "  
  <+> hsep (punctuate comma (map ppIdent clss)))
  
errDuplicateInstances :: [(QualIdent, QualIdent)] -> Message
errDuplicateInstances is
  = message (text "Two or more instances for the same class and type: "
  <+> (hsep $ punctuate comma $ 
       map (\(qid, tcon) -> parens $ ppQIdent qid <> comma <+> text (show tcon)) is))

errDuplicateTypeVars :: Position -> QualIdent -> TypeConstructor -> [Ident] -> Message
errDuplicateTypeVars p cls tcon ids
  = posMessage p 
     (text "Type variables appear more than once in instance definition of class"
      <+> ppQIdent cls <+> text "and type" <+> text (show tcon) <+> text ":"
      <+> (hsep $ punctuate comma $ map ppIdent ids))
      
      
errClassNameNotInScope :: Position -> QualIdent -> Message
errClassNameNotInScope p cls = posMessage p 
  (text "Error in instance declaration: Class name not in scope: " <> text (show cls))


errDataTypeNotInScope :: Position -> QualIdent -> Message
errDataTypeNotInScope p dt = posMessage p
  (text "Data type not in scope: " <> text (show dt))

errDataTypeHasIncorrectArity :: Position -> QualIdent -> Message
errDataTypeHasIncorrectArity p ty = posMessage p
  (text "Data type has incorrect arity in instance declaration: " <> text (show ty))
 
errDataTypeAmbiguous :: Position -> QualIdent -> Message
errDataTypeAmbiguous p id0 = posMessage p
  (text "Data type in instance declaration ambiguous: " <> text (show id0))
  
errContextVariableNotOnTheRightSide :: Position -> [Ident] -> String -> Message
errContextVariableNotOnTheRightSide p ids what = posMessage p $
  text "Variable(s)" <+> (hsep $ punctuate comma (map (text . escName) ids))
  <+> text ("in context, but not on the right side of the " ++ what)  
  
errMissingSuperClassInstances :: Position -> TypeConstructor -> [QualIdent] -> Message
errMissingSuperClassInstances p tycon clss = posMessage p $
  text "Missing superclass instances for type" <+> text (show tycon) <+>
  text "and the following classes:" <+> (hsep $ punctuate comma $ map (text . show) clss)

type SCon = [(QualIdent, Ident)]

showSCon :: SCon -> Doc
showSCon scon = parens $ hsep $ 
  punctuate comma (map (\(qid, ty) -> text (show qid) <+> text (show ty)) scon)

errContextNotImplied :: Position -> SCon -> SCon -> SCon -> Message
errContextNotImplied p thisContext _instsCxs notImplCxs = posMessage p $ 
  text ("Context of instance declaration doesn't imply contexts of instance declarations"
    ++ " for superclasses:") $$ text ("Context: ") <> (showSCon thisContext) $$
  text ("Not implied: ") <> (showSCon notImplCxs)  

errTypeInInstanceDecl :: Position -> QualIdent -> Message
errTypeInInstanceDecl p qid = posMessage p $ 
  text "Alias type in instance declaration: " <> text (show qid)

errNotAllowedTypeVars :: Position -> [Ident] -> Message
errNotAllowedTypeVars p ids = posMessage p $ 
  text ("Different type variables than the type variable given in the class declaration" ++ 
  " (currently) unfortunately not supported! ")
  $$ text "These are: " <> text (show ids)
    
errAmbiguousClassName :: Position -> QualIdent -> Message
errAmbiguousClassName p id0 = posMessage p $ 
  text "Ambiguous class name: " <> text (show id0) 
  
  