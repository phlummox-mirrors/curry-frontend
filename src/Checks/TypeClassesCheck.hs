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
    
    As the type signatures of the imported classes are already expanded, 
    we have to write out type signatures that are also expanded 
    in the code transformation. Since the type checker must expand non-expanded
    type signatures, but must not re-expand expanded type signatures again, 
    we provide a flag in all type signatures that indicates whether the 
    type signature has already been expanded. We have to be careful that
    we either provide completely unexpanded or completely expanded 
    type signatures. 
-}

module Checks.TypeClassesCheck (buildTypeSchemesNoExpand, typeClassesCheck) where

import Curry.Syntax.Type as ST hiding (IDecl)
import Env.ClassEnv
import Env.TypeConstructor
import Base.Messages (Message, message, posMessage, internalError)

import Data.List
import Text.PrettyPrint hiding (sep, isEmpty)
import Data.Maybe
import Control.Monad.State

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax.Utils
import Curry.Syntax.Pretty
import Base.CurryTypes
import Base.Types as BT (TypeScheme (..), polyType, constrainBy, Type (..), arrowArity
                        , typeSchemeToType)
import qualified Base.Types as BTC (Context) 
import Base.SCC
import Base.Utils (findMultiples, fst3, zipWith', fromJust')
import Base.Names
import Base.TopEnv
import qualified Data.Map as Map  

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
typeClassesCheck m decls0
    (ClassEnv importedClassesEnv importedInstances _ _) tcEnv0 = 
  case runTcc tcCheck initTccState of 
    ((newClasses, instances), []) -> 
      let -- add newly generated dictionary types to type constructor environment  
          tcEnv' = foldr (bindTC m tcEnv') tcEnv0 newDecls
          
          -- translate contexts, instances and classes:
          newDecls = adjustContexts m cEnv $ 
            concatMap (transformInstance m cEnv tcEnv') $ 
            concatMap (transformClass2 m cEnv tcEnv') decls
          
          -- build type schemes for all classes
          newClasses' = map (buildTypeSchemes True m tcEnv 
                          . renameTypeSigVars) newClasses
          importedClassesEnv' = 
            fmap (buildTypeSchemes False m tcEnv . renameTypeSigVars) importedClassesEnv
          
          -- construct class environment
          allClassesEnv = bindAll newClasses' importedClassesEnv'
          classMethodsEnv = constructClassMethodsEnv $ allClassBindings cEnv
          cEnv = ClassEnv allClassesEnv instances classMethodsEnv
                          (buildCanonClassMap allClassesEnv)
      in (newDecls, cEnv, [])
    (_, errs@(_:_)) -> (decls, ClassEnv emptyTopEnv [] emptyTopEnv Map.empty, errs)
  where
    decls = expandDerivingDecls decls0
    classDecls = filter isClassDecl decls
    instDecls = filter isInstanceDecl decls
    dataDecls = filter (\x -> isDataDecl x || isNewtypeDecl x) decls
    typeSigs = gatherTypeSigs decls
    tcEnv = foldr (bindTC m tcEnv) tcEnv0 decls
    tcCheck = do
      phase1
      hasErr1 <- hasError
      case hasErr1 of
        True -> return ([], [])
        False -> do
          phase2a
          hasErr2a <- hasError
          case hasErr2a of
            True -> return ([], [])
            False -> do
              phase2b
              hasErr2b <- hasError
              case hasErr2b of
                True -> return ([], [])
                False -> phase3

    -- ----------------------------------------------------------------------
    -- phase 1: checks that don't need the class environment
    -- ----------------------------------------------------------------------
    phase1 = do
      mapM_ typeVariableInContext classDecls
      mapM_ classMethodSigsContainTypeVar classDecls
      mapM_ instanceTypeVarsDoNotAppearTwice instDecls
      
      -- this test should be disabled when (in the far, far future) 
      -- class methods are allowed that have other type variables in their
      -- corresponding type signatures than the type variable of the class
      mapM_ checkCorrectTypeVarsInTypeSigs classDecls
      mapM_ checkContextsInClassMethodTypeSigs classDecls 
      
      -- mapM_ checkTypeVarsInContext classDecls -- checked above (typeVariableInContext)
      mapM_ checkTypeVarsInContext instDecls
      mapM_ checkTypeVarsInContext typeSigs 
      
      mapM_ (checkInstanceDataTypeCorrect m tcEnv) instDecls
      
      checkForDuplicateClassNames classDecls
      
      mapM_ (checkForDirectCycle m) classDecls
      
      noDoubleClassMethods m classDecls
      
      mapM_ checkEmptyDataTypeAndDeriving dataDecls
    
    -- ----------------------------------------------------------------------
    -- phase 2a: We test only that the deriving declarations are correct. 
    --           Thus we avoid many error messages in phase 2 b when these are
    --           not correct. 
    -- ----------------------------------------------------------------------
    phase2a = do
      let newClasses = map (classDeclToClass m) classDecls
          instances = map (localInst . instanceDeclToInstance m tcEnv) instDecls 
                      ++ importedInstances
          allClassesEnv = bindAll newClasses importedClassesEnv
          newClassEnv = ClassEnv allClassesEnv instances emptyTopEnv 
                                 (buildCanonClassMap allClassesEnv)
                                 
      mapM_ (checkClassesInDeriving m newClassEnv) dataDecls
    
    -- ----------------------------------------------------------------------
    -- phase 2b: Checks that need the class environment, but mostly only for
    --           determining whether a given class exists or not. Qualified
    --           instance/superclass contexts are not yet needed. 
    -- ----------------------------------------------------------------------
    phase2b = do 
      -- as in phase 2a
      let newClasses = map (classDeclToClass m) classDecls
          instances = map (localInst . instanceDeclToInstance m tcEnv) instDecls 
                      ++ importedInstances
          allClassesEnv = bindAll newClasses importedClassesEnv
          newClassEnv = ClassEnv allClassesEnv instances emptyTopEnv 
                                 (buildCanonClassMap allClassesEnv)
      
      -- TODO: check also contexts of (imported) classes and interfaces?
      mapM_ (checkClassesInContext m newClassEnv) classDecls
      mapM_ (checkClassesInContext m newClassEnv) instDecls
      -- check also contexts in typed expressions
      mapM_ (checkClassesInContext m newClassEnv) typeSigs
          
      mapM_ (checkRulesInInstanceOrClass m newClassEnv) instDecls
      mapM_ (checkRulesInInstanceOrClass m newClassEnv) classDecls
      
      mapM_ (checkClassNameInInstance m newClassEnv) instDecls
            
    -- ----------------------------------------------------------------------
    -- phase 3: checks that need the class environment, with
    --          qualified superclass/instance contexts 
    -- ----------------------------------------------------------------------
    phase3 = do  
      let newClasses' = 
            map (qualifyClass m newClassEnv' . classDeclToClass m) classDecls
          instances' =  
            map (localInst . qualifyInstance m newClassEnv' 
                           . instanceDeclToInstance m tcEnv) instDecls 
            ++ importedInstances
          allClassesEnv = bindAll newClasses' importedClassesEnv
          newClassEnv' = ClassEnv allClassesEnv instances' emptyTopEnv 
                                  (buildCanonClassMap allClassesEnv)
      
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
    origMethods = allMethods,
    methods = allMethods, 
    defaults = filter isFunctionDecl decls, 
    typeSchemes = [], 
    hidden = False, 
    publicMethods = map fst3 allMethods
  }
  where
    splitUpTypeSig :: Decl -> [Decl]
    splitUpTypeSig (TypeSig p e ids cx ty) 
      = map (\id0 -> TypeSig p e [id0] cx ty) ids
    splitUpTypeSig _ = internalError "splitUpTypeSig"
    allMethods = map (\(TypeSig _ _ [id0] cx ty) -> (id0, cx, ty)) $ 
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
    rules = decls, 
    origin = m }
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
    [] -> Nothing
    [DataType tc' _ _] -> Just tc'
    [RenamingType tc' _ _] -> Just tc'
    [AliasType _ _ _] -> Nothing
    _ -> case qualLookupTC (qualQualify m qid) tcEnv of
      [] -> Nothing
      [DataType tc' _ _] -> Just tc'
      [RenamingType tc' _ _] -> Just tc'
      [AliasType _ _ _] -> Nothing
      _ -> Nothing
tyConToQualIdent _ _ c = Just $ specialTyConToQualIdent c

-- |qualifies superclasses in the class context
qualifyClass :: ModuleIdent -> ClassEnv -> Class -> Class
qualifyClass m cEnv cls = 
  cls { superClasses = 
    map (getCanonClassName m cEnv)
        (superClasses cls) } 

-- |canonicalizes the class name: unqualified class names are qualified
-- with the module where the class is defined
getCanonClassName :: ModuleIdent -> ClassEnv -> QualIdent -> QualIdent
getCanonClassName m cEnv = fromJust . canonClassName m cEnv

-- |qualifies superclasses in the instance context and the class in the instance
-- declaration
qualifyInstance :: ModuleIdent -> ClassEnv -> Instance -> Instance
qualifyInstance m cEnv i = 
  i { context = map (\(qid, id0) -> (getCanonClassName m cEnv qid, id0)) (context i)
    , iClass = getCanonClassName m cEnv (iClass i) }   

-- |builds the canonical class map (a map from canonical class names to 
-- the corresponding classes)
buildCanonClassMap :: TopEnv Class -> Map.Map QualIdent Class
buildCanonClassMap classes = Map.fromList allClasses''
  where
  allClasses' = allClasses classes
  allClasses'' = map (\cls -> (theClass cls, cls)) allClasses'

-- | constructs the environment that maps class methods to classes  
constructClassMethodsEnv :: [(QualIdent, Class)] -> TopEnv Class
constructClassMethodsEnv bindings = 
  foldr bind emptyTopEnv classesAndMethods
  where
  classesAndMethods = 
    concatMap (\(c, cls) -> zip3 (repeat c) (repeat cls) (map fst3 $ methods cls))
      bindings
  bind :: (QualIdent, Class, Ident) -> TopEnv Class -> TopEnv Class
  bind (c, cls, m) env 
    | m `elem` publicMethods cls = 
      -- use as qualification for the method the qualification of the qualIdent
      -- under which the current class is stored. 
      qualImportTopEnv' (fromJust' "constructClassMethodsEnv" $ qidModule $ theClass cls)
        (qualifyLike c m) cls env
    | otherwise = env
       


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
gatherTS ts@(TypeSig _ _ _ _ _) = [ts]
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
gatherTSExpr (Typed _ expr cx texp) = gatherTSExpr expr ++ [typeSig False [] cx texp]
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
adjustContexts :: ModuleIdent -> ClassEnv -> [Decl] -> [Decl]
adjustContexts m cEnv ds = map (adjDecl m cEnv) ds

adjDecl :: ModuleIdent -> ClassEnv -> Decl -> Decl
adjDecl _ _    d@(InfixDecl _ _ _ _)   = d
adjDecl _ _    d@(DataDecl _ _ _ _ _)    = d
adjDecl _ _    d@(NewtypeDecl _ _ _ _ _) = d
adjDecl _ _    d@(TypeDecl _ _ _ _)    = d
adjDecl m cEnv   (TypeSig p e ids cx te) = TypeSig p e ids (canonContext m cEnv cx) te
adjDecl m cEnv   (FunctionDecl p cty n f eqs) = 
  FunctionDecl p cty n f (map (adjEqu m cEnv) eqs)
adjDecl _ _    d@(ForeignDecl _ _ _ _ _) = d
adjDecl _ _    d@(ExternalDecl _ _)      = d
adjDecl m cEnv   (PatternDecl p cty n pt rhs) = PatternDecl p cty n pt (adjRhs m cEnv rhs)
adjDecl _ _    d@(FreeDecl _ _) = d
adjDecl m cEnv   (ClassDecl p scon cls v ds) = 
  ClassDecl p scon cls v (adjustContexts m cEnv ds)
adjDecl m cEnv   (InstanceDecl p scon cls ty vs ds) = 
  InstanceDecl p scon cls ty vs (adjustContexts m cEnv ds)

adjEqu :: ModuleIdent -> ClassEnv -> Equation -> Equation
adjEqu m cEnv (Equation p lhs rhs) = Equation p lhs (adjRhs m cEnv rhs)

adjRhs :: ModuleIdent -> ClassEnv -> Rhs -> Rhs
adjRhs m cEnv (SimpleRhs p e ds) = 
  SimpleRhs p (adjExpr m cEnv e) (adjustContexts m cEnv ds)
adjRhs m cEnv (GuardedRhs ces ds) =
  GuardedRhs (map (adjCondExpr m cEnv) ces) (adjustContexts m cEnv ds)
 
adjCondExpr :: ModuleIdent -> ClassEnv -> CondExpr -> CondExpr
adjCondExpr m cEnv (CondExpr p e1 e2) = 
  CondExpr p (adjExpr m cEnv e1) (adjExpr m cEnv e2)

adjExpr :: ModuleIdent -> ClassEnv -> Expression -> Expression
adjExpr _ _    e@(Literal _) = e
adjExpr _ _    e@(Variable _ _) = e
adjExpr _ _    e@(Constructor _) = e
adjExpr m cEnv (Paren e) = Paren (adjExpr m cEnv e)
adjExpr m cEnv (Typed cty e cx ty) = 
  Typed cty (adjExpr m cEnv e) (canonContext m cEnv cx) ty
adjExpr m cEnv (Tuple sref es) = Tuple sref (map (adjExpr m cEnv) es)
adjExpr m cEnv (List sref es) = List sref (map (adjExpr m cEnv) es)
adjExpr m cEnv (ListCompr sref e ss) = 
  ListCompr sref (adjExpr m cEnv e) (map (adjStmt m cEnv) ss)
adjExpr m cEnv (EnumFrom e1) = EnumFrom (adjExpr m cEnv e1)
adjExpr m cEnv (EnumFromThen e1 e2) = EnumFromThen (adjExpr m cEnv e1) (adjExpr m cEnv e2)
adjExpr m cEnv (EnumFromTo e1 e2) = EnumFromTo (adjExpr m cEnv e1) (adjExpr m cEnv e2)
adjExpr m cEnv (EnumFromThenTo e1 e2 e3) = 
  EnumFromThenTo (adjExpr m cEnv e1) (adjExpr m cEnv e2) (adjExpr m cEnv e3)
adjExpr m cEnv (UnaryMinus i e) = UnaryMinus i (adjExpr m cEnv e)
adjExpr m cEnv (Apply e1 e2) = Apply (adjExpr m cEnv e1) (adjExpr m cEnv e2)
adjExpr m cEnv (InfixApply e1 op e2) = InfixApply (adjExpr m cEnv e1) op (adjExpr m cEnv e2)
adjExpr m cEnv (LeftSection e op) = LeftSection (adjExpr m cEnv e) op
adjExpr m cEnv (RightSection op e) = RightSection op (adjExpr m cEnv e)
adjExpr m cEnv (Lambda sref pts e) = Lambda sref pts (adjExpr m cEnv e)
adjExpr m cEnv (Let ds e) = Let (adjustContexts m cEnv ds) (adjExpr m cEnv e)
adjExpr m cEnv (Do ss e) = Do (map (adjStmt m cEnv) ss) (adjExpr m cEnv e)
adjExpr m cEnv (IfThenElse sref e1 e2 e3) = IfThenElse sref
  (adjExpr m cEnv e1) (adjExpr m cEnv e2) (adjExpr m cEnv e3)
adjExpr m cEnv (Case sref ct e alts) = 
  Case sref ct (adjExpr m cEnv e) (map (adjAlt m cEnv) alts)
adjExpr m cEnv (RecordConstr fs) = RecordConstr (map (adjField m cEnv) fs)
adjExpr m cEnv (RecordSelection e i) = RecordSelection (adjExpr m cEnv e) i
adjExpr m cEnv (RecordUpdate fs e) = 
  RecordUpdate (map (adjField m cEnv) fs) (adjExpr m cEnv e)   

adjStmt :: ModuleIdent -> ClassEnv -> Statement -> Statement
adjStmt m cEnv (StmtExpr sref e) = StmtExpr sref (adjExpr m cEnv e)
adjStmt m cEnv (StmtDecl ds) = StmtDecl (adjustContexts m cEnv ds)
adjStmt m cEnv (StmtBind sref p e) = StmtBind sref p (adjExpr m cEnv e)

adjAlt :: ModuleIdent -> ClassEnv -> Alt -> Alt
adjAlt m cEnv (Alt p pt rhs) = Alt p pt (adjRhs m cEnv rhs)

adjField :: ModuleIdent -> ClassEnv -> Field Expression -> Field Expression
adjField m cEnv (Field p i e) = Field p i (adjExpr m cEnv e)

-- |canonicalizes all classes in the given context: the given qualified class
-- name is replaced by the class name qualified with the module
-- where the class is in fact declared
canonContext :: ModuleIdent -> ClassEnv -> Context -> Context
canonContext m cEnv (Context cx) = 
  Context $ map 
    (\(ContextElem qid id0 tys) -> ContextElem (getCanonClassName m cEnv qid) id0 tys) cx

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
  mapM_ (checkClassOk m cEnv p) (map fst scon)
checkClassesInContext m cEnv (InstanceDecl p (SContext scon) _ _ _ _) = 
  mapM_ (checkClassOk m cEnv p) (map fst scon)
checkClassesInContext m cEnv (TypeSig p _ _ (Context cx) _) = 
  mapM_ (checkClassOk m cEnv p) (map (\(ContextElem qid _ _) -> qid) cx)
checkClassesInContext _ _ _ = internalError "TypeClassesCheck.checkClassesInContext"
    
-- |checks whether the given class (from a deriving declaration or a context)
-- is in scope and unambiguous
checkClassOk :: ModuleIdent -> ClassEnv -> Position -> QualIdent -> Tcc ()
checkClassOk m cEnv p qid = 
  case lookupNonHiddenClasses cEnv qid of 
    []    -> report (errClassNotInScope p qid)
    [_]   -> ok
    _     -> case lookupNonHiddenClasses cEnv (qualQualify m qid) of
      []  -> report (errAmbiguousClassName p qid) 
      [_] -> ok
      _   -> report (errAmbiguousClassName p qid) 

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
    tyVarInTypeSig tyvar (TypeSig p _ ids _con typeExpr) 
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
checkRulesInInstanceOrClass :: ModuleIdent -> ClassEnv -> Decl -> Tcc ()
checkRulesInInstanceOrClass m cEnv decl = 
  mapM_ isDefinedFunctionClassMethod (getDecls decl)
  where 
    isDefinedFunctionClassMethod (cls, FunctionDecl p _ _ f _) 
      = let ms = maybe [] methods (lookupClass m cEnv cls)
            eq = (\(id0, _, _) -> id0 == f)
        in 
        case find eq ms of
          Nothing -> report (errFunctionNoClassMethod p f)
          Just _ -> ok
    isDefinedFunctionClassMethod (_, TypeSig _ _ _ _ _) = ok
    isDefinedFunctionClassMethod _ = internalError "isDefinedFunctionClassMethod"

getDecls :: Decl -> [(QualIdent, Decl)]
getDecls (InstanceDecl _ _ cls _ _ decls) = zip (repeat cls) decls
getDecls (ClassDecl _ _ cls _ decls) = zip (repeat $ qualify cls) decls
getDecls _ = internalError "getDecls"

-- |Checks that there are no cycles in the class hierarchy. 
-- This can be determined by computing the strong connection components
-- and checking that each has only one element
checkForCyclesInClassHierarchy :: ClassEnv -> Tcc ()
checkForCyclesInClassHierarchy cEnv@(ClassEnv classes _ _ _) = 
  if all (==1) (map length sccs)
  then ok
  else mapM_ (report . errCyclesInClassHierarchy) (filter (\xs -> length xs > 1) sccs)
  where 
    sccs = scc (\qid -> [qid]) 
               (\qid -> (superClasses $ fromJust $ canonLookupClass cEnv qid))
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


-- |Checks that there is at most one local instance for a given class and type
checkForDuplicateInstances :: ClassEnv -> Tcc ()
checkForDuplicateInstances cEnv
  = let duplInstances 
          = findMultiples $ map (\i -> (iClass i, iType i)) (getLocalInstances cEnv)
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
checkClassNameInInstance :: ModuleIdent -> ClassEnv -> Decl -> Tcc ()
checkClassNameInInstance m cEnv (InstanceDecl p _ cls _ _ _) = 
  checkClassOk m cEnv p cls
checkClassNameInInstance _ _ _ = internalError "checkClassNameInScope"

-- |Checks whether the instance data type is in scope and not a type synonym. 
-- Check also that the arity of the data type in the instance declaration
-- is correct. 
checkInstanceDataTypeCorrect :: ModuleIdent -> TCEnv -> Decl -> Tcc ()
checkInstanceDataTypeCorrect m tcEnv (InstanceDecl p _ _ (QualTC qid) ids _) = do
  tinfo <- case qualLookupTC qid tcEnv of
    [] -> report (errDataTypeNotInScope p qid) >> return []
    [AliasType _ _ _] -> report (errTypeInInstanceDecl p qid) >> return []
    info@[_] -> return info
    _ -> case qualLookupTC (qualQualify m qid) tcEnv of
      [] -> report (errDataTypeAmbiguous p qid) >> return []
      [AliasType _ _ _] -> report (errTypeInInstanceDecl p qid) >> return []
      info@[_] -> return info
      _ -> report (errDataTypeAmbiguous p qid) >> return []
      
  when ((not $ null tinfo) && tcArity (head tinfo) /= length ids) $ 
    report (errDataTypeHasIncorrectArity p qid)  

checkInstanceDataTypeCorrect _ _ (InstanceDecl p _ _ UnitTC ids _) = 
  unless (null ids) $ report (errDataTypeHasIncorrectArity p qUnitId)
checkInstanceDataTypeCorrect _ _ (InstanceDecl p _ _ (TupleTC n) ids _) =
  unless (length ids == n) $ report (errDataTypeHasIncorrectArity p (qTupleId n))
checkInstanceDataTypeCorrect _ _ (InstanceDecl p _ _ ListTC ids _) =
  unless (length ids == 1) $ report (errDataTypeHasIncorrectArity p qListId)
checkInstanceDataTypeCorrect _ _ (InstanceDecl p _ _ ArrowTC ids _) =
  unless (length ids == 2) $ report (errDataTypeHasIncorrectArity p qArrowId)  
checkInstanceDataTypeCorrect _ _ _ = internalError "checkInstanceDataTypeCorrect"

-- |Checks that there are only type vars in the context that also appear on
-- the right side
checkTypeVarsInContext :: Decl -> Tcc ()
checkTypeVarsInContext (TypeSig p _ _ids cx tyexp) = 
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
        scs = allSuperClasses cEnv (getCanonClassName m cEnv cls)
        tyId = tyConToQualIdent m tcEnv ty
        insts = map (\c -> getInstance cEnv c (fromJust tyId)) scs 
        missingInsts = map fst $ filter (isNothing . snd) $ zip scs insts in
    when (isJust tyId) $ unless (all isJust insts) $ report $ 
      errMissingSuperClassInstances p ty missingInsts      
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses _ _ _ _
  = internalError "checkForInstanceDataTypeExistAlsoInstancesForSuperclasses"
  
-- |returns the instance from the class environment for the given instance
-- declaration. This function must be called only after it has been checked
-- that as well the class name and the type name are valid (i.e., in phase 3)
getInstance' :: ModuleIdent -> ClassEnv -> TCEnv -> Decl -> Instance
getInstance' m cEnv tcEnv (InstanceDecl _p (SContext _scon) cls ty _tyvars _) =
  inst 
  where 
  tyId = fromJust $ tyConToQualIdent m tcEnv ty
  cls' = getCanonClassName m cEnv cls
  inst = fromJust $ getInstance cEnv cls' tyId
getInstance' _ _ _ _ = internalError "getInstance'"

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
    inst@(InstanceDecl p _scon cls ty _tyvars _)
  = let inst' = getInstance' m cEnv tcEnv inst
        thisContext = getContextFromInst inst'
        scs = allSuperClasses cEnv (getCanonClassName m cEnv cls)
        tyId = tyConToQualIdent m tcEnv ty
        insts = map fromJust $ filter isJust $ 
          map (\c -> getInstance cEnv c (fromJust tyId)) scs
        instCxs = concatMap getContextFromInst insts
        
        thisContext' = getSContextFromContext thisContext (typeVars inst')
        instCxs' = getSContextFromContext instCxs (typeVars inst')
        notImplCxs = (filter (not . implies cEnv thisContext) instCxs)
        notImplCxs' = getSContextFromContext notImplCxs (typeVars inst') in
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
  tyVars (TypeSig p _ _ _ te) = (p, typeVarsInTypeExpr te)
  tyVars _ = internalError "checkTypeVarsInTypeSigs"
  checkTypeVars (p, tyvars) = 
    when (nub tyvars /= [tyvar] && not (null $ nub tyvars)) $ 
      report $ errNotAllowedTypeVars p (nub tyvars \\ [tyvar])
checkCorrectTypeVarsInTypeSigs _ = internalError "checkCorrectTypeVarsInTypeSigs"

-- |Check that there are no contexts in the type signatures of class methods
-- (currently not supported)  
checkContextsInClassMethodTypeSigs :: Decl -> Tcc ()
checkContextsInClassMethodTypeSigs (ClassDecl _ _ _ _ ds)
  = mapM_ checkTySig tySigs
  where
  tySigs = filter isTypeSig ds
  checkTySig (TypeSig p _ ids (Context cx) _) = 
    unless (null cx) $ report $ errNonEmptyContext p ids
  checkTySig _ = internalError "checkContextsInClassMethodTypeSigs"
checkContextsInClassMethodTypeSigs _ = internalError "checkContextsInClassMethodTypeSigs"

-- |checks that we don't use deriving for data types without constructors
checkEmptyDataTypeAndDeriving :: Decl -> Tcc ()
checkEmptyDataTypeAndDeriving (DataDecl    _ _ _ _ Nothing) = ok
checkEmptyDataTypeAndDeriving (NewtypeDecl _ _ _ _ Nothing) = ok
checkEmptyDataTypeAndDeriving (DataDecl p ty _ cs (Just (Deriving ds))) = 
  when (null cs && not (null ds)) $ report $ errEmptyDataTypeDeriving p ty
-- Newtype declaration has always a constructor!
checkEmptyDataTypeAndDeriving (NewtypeDecl _ _ _ _ (Just (Deriving _))) = ok
checkEmptyDataTypeAndDeriving _ = internalError "checkEmptyDataTypeAndDeriving"

-- |Checks that the classes in the deriving declaration of a data type are
-- in scope and unambiguous. It tests furtherly, whether the classes are 
-- supported. 
checkClassesInDeriving :: ModuleIdent -> ClassEnv -> Decl -> Tcc ()
checkClassesInDeriving _m _cEnv (DataDecl    _ _ _ _ Nothing) = ok
checkClassesInDeriving _m _cEnv (NewtypeDecl _ _ _ _ Nothing) = ok
checkClassesInDeriving m cEnv (DataDecl    p ty _ _ (Just (Deriving clss))) = do
  mapM_ (checkClassOk m cEnv p) clss
  mapM_ (checkSupported m cEnv p ty) clss
checkClassesInDeriving m cEnv (NewtypeDecl p ty _ _ (Just (Deriving clss))) = do
  mapM_ (checkClassOk m cEnv p) clss
  mapM_ (checkSupported m cEnv p ty) clss
checkClassesInDeriving _ _ _ = internalError "checkClassesInDeriving"

-- |checks whether we can derive an instance for the given class
checkSupported :: ModuleIdent -> ClassEnv -> Position -> Ident -> QualIdent -> Tcc ()
checkSupported m cEnv p ty cls = 
  case lookupClass m cEnv cls of 
    Nothing -> ok -- error message for this case already issued
    Just c -> unless (theClass c `elem` supportedDerivingClasses) $
      report $ errNotSupportedDerivingClass p ty cls 

-- |the classes for which deriving is supported
supportedDerivingClasses :: [QualIdent]
supportedDerivingClasses = 
  [ eqClsIdent 
  , ordClsIdent
  -- , showClsIdent -- not yet
  -- , readClsIdent -- not yet
  ]

-- ---------------------------------------------------------------------------
-- source code transformation
-- ---------------------------------------------------------------------------
{-
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
-}

-- |Transforms class declarations using tuples as dictionaries. This handles
-- class methods with other type variables than the type variable given in the class
-- declaration well (?)
transformClass2 :: ModuleIdent -> ClassEnv -> TCEnv -> Decl -> [Decl]
transformClass2 mdl cEnv tcEnv (ClassDecl p _scx cls _tyvar _decls) = 
  genDictType
  : concatMap genSuperClassDictSelMethod superClasses0
  ++ concatMap genMethodSelMethod (zip methods0 [0..])
  ++ concatMap genNonDirectSuperClassDictSelMethod nonDirectSuperClasses
  ++ concatMap genDefaultMethod (defaults theClass0)
  where
  theClass0 = fromJust $ lookupLocalClass cEnv (qualify cls)
  superClasses0 = map show $ superClasses theClass0
  superClasses1 = superClasses theClass0
  methods0 = methods theClass0
  nonDirectSuperClasses = allSuperClasses cEnv (theClass theClass0) \\ superClasses1
  
  -- | Generates functions for extracting (direct) super class dictionaries 
  -- from a given dictionary
  genSuperClassDictSelMethod :: String -> [Decl]
  genSuperClassDictSelMethod scls = 
    let selMethodName = mkSelFunName (show $ theClass theClass0) scls in
    [ superClassSelMethodTypeSig selMethodName scls
    , fun (mkIdent selMethodName)
      [equation
        (equationLhs selMethodName)
        (simpleRhs (qVar $ dictSelParam selMethodName scls))
      ]
    ]
    
  -- | Generates functions for extracting the class functions from a given 
  -- dictionary
  genMethodSelMethod :: ((Ident, Context, TypeExpr), Int) -> [Decl]
  genMethodSelMethod ((m, _cx, ty), i) = 
    let selMethodName = mkSelFunName (show $ theClass theClass0) (show m) in
    [ typeSig True [mkIdent selMethodName]
      emptyContext
      (ArrowType 
        (genDictTypeExpr mdl tcEnv (show $ theClass theClass0) (typeVar theClass0))
        (if not zeroArity then ty else ArrowType (expandedUnit mdl tcEnv) ty)
      )
    , fun (mkIdent selMethodName)
      [equation
        (equationLhs selMethodName)
        (simpleRhs (qVar $ methodSelParam selMethodName i))
      ]
    ]
    where 
    zeroArity = arrowArity 
      (typeSchemeToType $ fromJust $ 
        canonLookupMethodTypeScheme' cEnv (theClass theClass0) m) == 0
  
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
    [ superClassSelMethodTypeSig selMethodName (show scls)
    , fun (mkIdent selMethodName)
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
  
  -- |Generates a top-level function containing the implementation of the
  -- default implementation given in the class declaration
  genDefaultMethod :: Decl -> [Decl]
  genDefaultMethod (FunctionDecl _p cty n f eqs) = 
    TypeSig p True [rename toTopLevel f] cx ty' : 
      [FunctionDecl p cty n (rename toTopLevel f) (map (transEqu zeroArity toTopLevel) eqs)] 
    where
    (cx0, ty) = fromJust $ canonLookupMethodTypeSig' cEnv (theClass theClass0) f
    cx = combineContexts cx0 
          (Context [ContextElem (theClass theClass0) (typeVar theClass0) []])
    toTopLevel :: RenameFunc
    toTopLevel f0 = defMethodName (theClass theClass0) f0
    zeroArity = arrowArityTyExpr ty == 0 
    ty' = if zeroArity then ArrowType (expandedUnit mdl tcEnv) ty else ty
    
  genDefaultMethod _ = internalError "genDefaultMethod"

  -- |generates a type declaration for the type of the dictionary for the given class  
  genDictType :: Decl
  genDictType = 
    TypeDecl p (mkIdent $ mkDictTypeName $ show (theClass theClass0))
             [typeVar theClass0] (dictTypeExpr mdl cEnv tcEnv (theClass theClass0))
  
  -- |generates the typesignature of a superclass selection method
  superClassSelMethodTypeSig :: String -> String -> Decl
  superClassSelMethodTypeSig selMethodName scls =
    typeSig True [mkIdent selMethodName]
      emptyContext
      (ArrowType 
        (genDictTypeExpr mdl tcEnv (show $ theClass theClass0) (mkIdent var))
        (genDictTypeExpr mdl tcEnv scls (mkIdent var))
      )
    where var = "a"
  
  -- the renamings are important so that the parameters are not handled as
  -- global functions. Also important is that the parameters are globally
  -- unique
  dictSelParam selMethodName s = flip renameIdent 1 $ 
    mkIdent (identPrefix ++ selMethodName ++ sep ++ s)
  methodSelParam selMethodName n = flip renameIdent 1 $ 
    mkIdent (identPrefix ++ selMethodName ++ sep ++ "x" ++ (show n))
  
  
transformClass2 _ _ _ d = [d]

-- |generates a type expression that represents the type of the dictionary 
-- of the given class 
genDictTypeExpr :: ModuleIdent -> TCEnv -> String -> Ident -> TypeExpr
genDictTypeExpr m tcEnv theClass0 var = expandTypeExpr m tcEnv $  
  (ConstructorType (mkQIdent $ mkDictTypeName $ theClass0)
    [VariableType var])

type IDecl = Decl

-- |as we have to be careful to provide *expanded* type signatures, we 
-- have to expand the unit type as well
expandedUnit :: ModuleIdent -> TCEnv -> TypeExpr
expandedUnit mdl tcEnv = (expandTypeExpr mdl tcEnv $ TupleType [])

-- |returns a type expression representing the type of the dictionary for
-- the given class (here the canonicalized name must be given). Note that
-- the resulting type expression is completely unexpanded (using
-- dictionary types and the original method signatures). It follows that
-- this function can only be used for classes from the source file being compiled,
-- not for classes that are imported.
dictTypeExpr :: ModuleIdent -> ClassEnv -> TCEnv -> QualIdent -> TypeExpr
dictTypeExpr m cEnv tcEnv cls =
  case null (scsTypes ++ methodTypes) of
    True -> TupleType [] -- unit
    False -> case length (scsTypes ++ methodTypes) == 1 of
      True -> case length scsTypes == 1 of
        True -> head scsTypes
        False -> head methodTypes
      False -> TupleType (scsTypes ++ methodTypes)
  where
  c = fromJust $ canonLookupClass cEnv cls
  scs = superClasses c
  theMethods = origMethods c

  scsTypes = map (\cls0 -> ConstructorType
                             (qualify $ mkIdent $ mkDictTypeName $ show cls0)
                             [VariableType $ typeVar c]) scs
  methodTypes = map considerZeroArity theMethods

  considerZeroArity :: (Ident, Context, TypeExpr) -> TypeExpr
  considerZeroArity (_m, _cx, ty) = 
    -- we have to expand the type because there could be type synonyms in 
    -- the class methods that hide the fact that the arity isn't zero. Example:
    -- 
    -- type Fun a = a -> a
    -- class Arb a where
    --   arb :: Fun a
    -- 
    -- Here without expanding the compiler would erronously assume an arity
    -- of zero. 
    if arrowArity (expandType m tcEnv $ toType [] ty) /= 0
    then ty
    else ArrowType (TupleType []) ty

-- ----------------------------------------------------------------------------

-- |transformInstance creates top level functions for the methods 
-- of which rules are given in the instance declaration, and concrete 
-- dictionaries, as well as type signatures for the instance rules. 
transformInstance :: ModuleIdent -> ClassEnv -> TCEnv -> IDecl -> [Decl]
transformInstance m cEnv tcEnv idecl@(InstanceDecl _ _ cls tycon _ decls)
  = concatMap (transformMethod m cEnv tcEnv idecl ity) decls
  ++ concatMap (handleMissingFunc m cEnv idecl ity) missingMethods
  -- create dictionary 
  ++ createDictionary2 m cEnv tcEnv idecl ity
  where
  ity = fromJust $ tyConToQualIdent m tcEnv tycon
  presentMethods = nub $ map (\(FunctionDecl _ _ _ id0 _) -> id0) decls
  theClass0 = fromJust $ lookupClass m cEnv cls 
  theMethods0 = nub $ map fst3 $ methods theClass0
  missingMethods = theMethods0 \\ presentMethods
transformInstance _ _ _ d = [d]

-- |transforms one method defined in an instance to a top level function 
transformMethod :: ModuleIdent -> ClassEnv -> TCEnv -> IDecl -> QualIdent -> Decl -> [Decl]
transformMethod m cEnv tcEnv idecl@(InstanceDecl _ _ cls _ _ _) ity
                     decl@(FunctionDecl _ _ _ _ _) =
  -- create type signature
  createTypeSignature m rfunc cEnv tcEnv idecl decl
  -- create function rules
  : [createTopLevelFuncs m cEnv rfunc idecl decl] 
  where 
    cls' = getCanonClassName m cEnv cls
    -- rename for specific instance!
    rfunc = (\s -> instMethodName cls' ity s)
transformMethod _ _ _ _ _ _ = internalError "transformMethod"

-- |create a name for the (hidden) function that is implemented by the  
-- function definitions in the instance  
instMethodName :: QualIdent -> QualIdent -> String -> String
instMethodName cls tcon s = implPrefix ++ show cls ++ sep ++ show tcon ++ sep ++ s

-- |create a name for the default method in a class declaration
defMethodName :: QualIdent -> String -> String
defMethodName cls fun0 = mkDefFunName (show cls) fun0

-- |creates a type signature for an instance method which is transformed to
-- a top level function
createTypeSignature :: ModuleIdent -> RenameFunc -> ClassEnv -> TCEnv -> IDecl -> Decl -> Decl
createTypeSignature m rfunc cEnv tcEnv (InstanceDecl _ scx cls tcon tyvars _) 
                    (FunctionDecl p _ _ f _eqs) 
  = TypeSig p True [rename rfunc f] cx' ty''
  where
    (cx, ty) = fromJust $ lookupMethodTypeSig' m cEnv cls f 
    theClass_ = fromJust $ lookupClass m cEnv cls
     
    -- Substitute class typevar with given instance type. 
    -- Rename tyvars, so that they do not equal type vars in the class
    -- method type signature, like in the following example:
    -- class C a where fun :: a -> b -> Bool
    -- instance Eq b => C (S b) where fun = ...
    -- Important: expand the type!
    theType = expandTypeExpr m tcEnv $ 
      SpecialConstructorType tcon (map (VariableType . flip renameIdent 1) tyvars)
    
    subst = [(typeVar theClass_, theType)]
    -- cx' = substInContext subst cx
    ty' = substInTypeExpr subst ty
    ty'' = if arrowArityTyExpr ty' == 0 then ArrowType (expandedUnit m tcEnv) ty' else ty'
    
    -- add instance context. The variables have to be renamed here as well
    renamedSContext = (\(SContext elems) -> 
      SContext $ map (\(qid, id0) -> (qid, renameIdent id0 1)) elems) scx
    icx = simpleContextToContext renamedSContext
    cx' = combineContexts icx cx
createTypeSignature _ _ _ _ _ _ = internalError "createTypeSignature"    

combineContexts :: ST.Context -> ST.Context -> ST.Context
combineContexts (Context e1) (Context e2) = Context (e1 ++ e2)

type RenameFunc = String -> String

-- |All concrete implementations of class methods in an instance declaration are
-- shifted by this function to top level, using new generated function names
-- for the definitions. 
createTopLevelFuncs :: ModuleIdent -> ClassEnv -> RenameFunc -> IDecl -> Decl -> Decl
createTopLevelFuncs m cEnv rfunc (InstanceDecl _ _ cls _ _ _) 
                               (FunctionDecl p cty n id0 eqs) 
  = FunctionDecl p cty n (rename rfunc id0) (map (transEqu zeroArity rfunc) eqs)
  where
  (_, ty) = fromJust $ lookupMethodTypeSig' m cEnv cls id0
  zeroArity = arrowArityTyExpr ty == 0
createTopLevelFuncs _ _ _ _ _ = internalError "createTopLevelFuncs"

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

-- |handles functions missing in an instance declaration. Searches first for a
-- default method, and if none present, inserts an error statement
handleMissingFunc :: ModuleIdent -> ClassEnv -> IDecl -> QualIdent -> Ident -> [Decl]
handleMissingFunc m cEnv (InstanceDecl _ _ cls _tcon _ _) ity fun0 = 
  if not defaultMethodDefined then [ fun globalName [equ1] ] else []
  where
  cls' = getCanonClassName m cEnv cls
  globalName = mkIdent $ instMethodName cls' ity (show fun0)
  equ1 = equation (FunLhs globalName []) 
    (simpleRhs (Apply (qVar . mkIdent $ "error") 
                      (Literal $ String (srcRef 0) errorString)))
  errorString = show fun0 ++ " not given in instance declaration of class "
    ++ show cls' ++ " and type " ++ show ity
  theClass0 = fromJust $ lookupClass m cEnv cls
  defaultMethodDefined = fun0 `elem` getDefaultMethods theClass0
  
handleMissingFunc _ _ _ _ _ = internalError "handleMissingFunc"

{-
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
-}

-- |This function creates a dictionary for the given instance declaration, 
-- using tuples
createDictionary2 :: ModuleIdent -> ClassEnv -> TCEnv -> IDecl -> QualIdent -> [Decl]
createDictionary2 m cEnv tcEnv (InstanceDecl _ scx cls0 tcon tvars decls) ity = 
  [ typeSig True [dictName cls] 
      (if isEmpty then ST.emptyContext else simpleContextToContext scx) dictType0
  , fun (dictName cls)
    [equation
      (FunLhs (dictName cls) [])
      (simpleRhs 
        (if length all0 == 1 then head all0 else Tuple noRef all0))
      ]
  ] 
  where
  cls = getCanonClassName m cEnv cls0
  dictName c = mkIdent $ mkDictName (show c) (show ity)
  theClass0 = fromJust $ lookupClass m cEnv cls0
  superClasses0 = superClasses theClass0
  methods0 = methods theClass0
  defaultMethods = getDefaultMethods theClass0
  scs = map (qVar . dictName) superClasses0
  ms = map (qVar . mkIdent . correctName . fst3) methods0
  correctName :: Ident -> String
  correctName s
    | s `elem` defaultMethods && not (methodImplPresent s) = 
      defMethodName cls (show s)
    | otherwise = instMethodName cls ity (show s)
  all0 = scs ++ ms
  
  dictType0 = expandTypeExpr m tcEnv $  
    (ConstructorType (mkQIdent $ mkDictTypeName $ show $ theClass theClass0)
    $ [SpecialConstructorType tcon (map VariableType tvars)]) 
    
  methodImplPresent :: Ident -> Bool
  methodImplPresent f = f `elem` map (\(FunctionDecl _ _ _ f0 _) -> f0) decls
  
  -- if dictionaries are empty, i.e., they don't contain any class methods (both
  -- from the class itself and the superclasses), we would get ambiguous
  -- context elements if we don't remove the context completely. It is 
  -- important that in the "dictCode" function of the class environment, 
  -- this removal of the whole context is reflected.
  isEmpty = isEmptyDict cEnv cls
  -- or equivalent:  
  -- isEmpty = null $ typeVarsInTypeExpr dictType0
  
createDictionary2 _ _ _ _ _ = internalError "createDictionary"

-- ---------------------------------------------------------------------------
-- source code transformations related to "deriving" of instances
-- ---------------------------------------------------------------------------

-- | expand all data declarations with a deriving annotation in the given list
expandDerivingDecls :: [Decl] -> [Decl]
expandDerivingDecls ds = ds ++ concatMap expandDerivingDecl dataDecls
  where
  dataDecls = filter (\d -> isDataDecl d || isNewtypeDecl d) ds
  
-- | create all derived instances for the given data/newtype declaration 
expandDerivingDecl :: Decl -> [Decl]
expandDerivingDecl d = if isNothing maybeDeriv 
  then []
  else
    concatMap (createInstance d) classes
  where
  maybeDeriv = getDeriving d
  Deriving classes = fromJust maybeDeriv

-- |retrieve the deriving part of a newtype/data declaration
getDeriving :: Decl -> Maybe Deriving
getDeriving (NewtypeDecl _ _ _ _ d) = d
getDeriving (DataDecl _ _ _ _ d) = d
getDeriving _ = internalError "getDeriving"

-- |creates an instance for the given data declaration and the given class
createInstance :: Decl -> QualIdent -> [Decl]
createInstance d cls = 
  -- consider only the *name* of the class, not the module identifier. If 
  -- this is wrong, it will be detected later
  if unqualify cls == unqualify eqClsIdent
  then [createEqInstance d cls]
  else if unqualify cls == unqualify ordClsIdent
  then [createOrdInstance d cls]
  else []
  -- TODO: add further instances here

-- |creates an Eq or an Ord instance for the given data declaration
createEqOrOrdInstance :: Decl      -- ^ the data/newtype declaration 
                      -> Ident     -- ^ the "==" or the "<=" operator
                      -> QualIdent -- ^ the class for which the instance is build
                      -- | the generation function for the right hand sides of the equations. 
                      -- Takes the two constructors and their positions in the 
                      -- data declaration, as well as the arities of the constructors 
                      -> (Position -> (Ident, Int) -> (Ident, Int) -> Int -> Int -> [Ident] -> [Ident] -> Rhs)
                      -> String  -- ^ the prefix to be used for parameters
                      -> Decl    -- ^ the resulting instance declaration
createEqOrOrdInstance (DataDecl p ty dataVars cons _) op clsIdent genRhs prefix = 

  InstanceDecl p (SContext scon) cls tycon vars 
    [FunctionDecl p Nothing (-1) op eqs]
  
  where
  scon = map (\v -> (clsIdent, v)) dataVars
  cls = clsIdent
  tycon = QualTC $ qualify ty
  vars = dataVars
  
  eqs = concatMap (\(c, n) -> map (\(c', n') -> genEq c c' n n') cons') cons' 
  
  -- record the respective number for each constructor, because we need the order of 
  -- the constructors for the Ord instance
  cons' = map getCon (zip [0..] cons)
  
  -- |get the data constructor and its arity from the given constructor declaration
  getCon :: (Int, ConstrDecl) -> ((Ident, Int), Int)
  getCon (i, ConstrDecl _ _ c tes) = ((c, i), length tes)
  getCon (i, ConOpDecl  _ _ _ c _) = ((c, i), 2)
  
  -- |generate for each constructor pair (C_i, C_j) an equation. If C_i == C_j, 
  -- then compare the parameters of the constructors, else return False. 
  -- Note: here for /all/ constructor pairs must an equation be created, 
  -- else we would get overlapping rules and thus unwanted non-determinism. 
  genEq :: (Ident, Int) -> (Ident, Int) -> Int -> Int -> Equation 
  genEq (c, i) (c', i') n n' = Equation p 
      (FunLhs op [ConstructorPattern (qualify c) (map VariablePattern newVars), 
                  ConstructorPattern (qualify c') (map VariablePattern newVars')])
      (genRhs p (c, i) (c', i') n n' newVars newVars') 
    where
    newVars  = map (mkIdent' . makeName) [1..n]
    newVars' = map (mkIdent' . (++ "'") . makeName) [1..n']
    makeName i0 = prefix ++ show c ++ sep ++ show c' ++ sep ++ show i0
  
  -- |the renaming of the identifiers is important so that the parameters
  -- are not handled as top level functions. 
  mkIdent' :: String -> Ident
  mkIdent' = flip renameIdent 1 . mkIdent

createEqOrOrdInstance (NewtypeDecl p ty vars (NewConstrDecl p' vars' id' ty') d) 
                       op clsIdent genRhs prefix =
  -- newtype declarations are simply treated as data declarations with 
  -- one constructor.  
  createEqOrOrdInstance (DataDecl p ty vars [ConstrDecl p' vars' id' [ty']] d) 
                        op clsIdent genRhs prefix
createEqOrOrdInstance _ _ _ _ _ = internalError "createEqOrOrdInstance"

-- |creates an "Eq" instance for the given data type
createEqInstance :: Decl -> QualIdent -> Decl
createEqInstance d cls = createEqOrOrdInstance d eqOp cls genEqRhs deriveEqPrefix

-- |generates the right hand sides used in the derived Eq instance  
genEqRhs :: Position -> (Ident, Int) -> (Ident, Int) -> Int -> Int -> [Ident] -> [Ident] -> Rhs
genEqRhs p (c, _) (c', _) n _n' newVars newVars' = 
  SimpleRhs p (if c == c' then compareExpr else Constructor $ qualify falseCons) []
  where
  -- |creates the comparison expression for the parameters of the constructors
  -- (or @True@ if none present)
  compareExpr :: Expression
  compareExpr = 
    let vars0 = zipWith' (,) newVars newVars' 
        (firstVar, firstVar') = head vars0 in
    if n == 0 then Constructor $ qualify trueCons
    else foldl (\el (v, v') -> InfixApply el infixAndOp 
                 (InfixApply (qVar v) infixEqOp (qVar v'))) 
               (InfixApply (qVar firstVar) infixEqOp (qVar firstVar'))
               (tail vars0)

-- |creates an "Ord" instance for the given data type
createOrdInstance :: Decl -> QualIdent -> Decl
createOrdInstance d cls = createEqOrOrdInstance d leqOp cls genOrdRhs deriveOrdPrefix

-- |generates the right hand sides used in the derived Ord instance. The scheme
-- is as follows:
-- Consider @C_i ... <= C_j ...@:
-- i < j: Result is True
-- i > j: Result is False
-- i == j: We have the following situation:
--   C_i e_1 ... e_n <= C_i e_1' ... e_n'
--   if n == 0: Result is True
--   else compare lexicographically e_1 to e_n: Result is: 
--        e_1 < e_1' || 
--        e_1 == e_1' && e_2 < e2' ||
--        e_1 == e_2' && e_2 == e_2' && e_3 < e_3' ||
--        ...
--        e_1 == e_2' && ... && e_(n-1) == e_(n-1)' && e_n <= e_n' 
-- Note that in "e_n <= e_n'" a "<=" is used, not a "<"!
genOrdRhs :: Position -> (Ident, Int) -> (Ident, Int) -> Int -> Int -> [Ident] -> [Ident] -> Rhs
genOrdRhs p (_c, i0) (_c', i0') n _n' newVars newVars' = 
  SimpleRhs p 
    (if i0 < i0' 
     then Constructor $ qualify trueCons
     else if i0 > i0'
     then Constructor $ qualify falseCons
     else 
     
       if n == 0 then Constructor $ qualify trueCons
       else foldl1 (\e e' -> InfixApply e infixOrOp e') (map (createForN n) [1..n])
    ) []
  where 
  createForN :: Int -> Int -> Expression
  createForN numAll i 
    = foldl1 (\e e' -> InfixApply e infixAndOp e') (map createForI [1..i])
    where
    createForI :: Int -> Expression
    createForI k 
      | k < i                 = InfixApply v infixEqOp   v' -- e_k == e_k'
      | k == i && k /= numAll = InfixApply v infixLessOp v' -- e_k <  e_k'
      | k == i && k == numAll = InfixApply v infixLeqOp  v' -- e_k <= e_k'
      | otherwise = internalError "genOrdRhs" 
      where
      v  = Variable Nothing $ qualify $ newVars  !! (k-1)
      v' = Variable Nothing $ qualify $ newVars' !! (k-1)
     

-- ---------------------------------------------------------------------------

eqClsIdentName :: String
eqClsIdentName = "Eq"

ordClsIdentName :: String
ordClsIdentName = "Ord"

eqClsIdent :: QualIdent
eqClsIdent = qualifyWith tcPreludeMIdent (mkIdent eqClsIdentName) 

ordClsIdent :: QualIdent
ordClsIdent = qualifyWith tcPreludeMIdent (mkIdent ordClsIdentName)

eqOp :: Ident
eqOp = mkIdent "=="

leqOp :: Ident
leqOp = mkIdent "<="

lessOp :: Ident
lessOp = mkIdent "<"

andOp :: Ident
andOp = mkIdent "&&"

orOp :: Ident
orOp = mkIdent "||"

infixEqOp :: InfixOp
infixEqOp = InfixOp Nothing $ qualify $ eqOp

infixLeqOp :: InfixOp
infixLeqOp = InfixOp Nothing $ qualify $ leqOp

infixLessOp :: InfixOp
infixLessOp = InfixOp Nothing $ qualify $ lessOp

infixAndOp :: InfixOp
infixAndOp = InfixOp Nothing $ qualify $ andOp

infixOrOp :: InfixOp
infixOrOp = InfixOp Nothing $ qualify $ orOp

-- **** TODO **** proper qualification (Prelude!)
trueCons :: Ident
trueCons = mkIdent "True"

-- **** TODO **** proper qualification (Prelude!)
falseCons :: Ident
falseCons = mkIdent "False"

deriveEqPrefix :: String
deriveEqPrefix = identPrefix ++ "drvEq" ++ sep

deriveOrdPrefix :: String
deriveOrdPrefix = identPrefix ++ "drvOrd" ++ sep

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

typeSig :: Bool -> [Ident] -> Context -> TypeExpr -> Decl
typeSig = TypeSig NoPos

simpleRhs :: Expression -> Rhs
simpleRhs e = SimpleRhs NoPos e []

-- |expands the given type expression by converting it first to a "Type", 
-- expanding the "Type", and then re-converting it back to a "TypeExpr"
expandTypeExpr :: ModuleIdent -> TCEnv -> TypeExpr -> TypeExpr
expandTypeExpr m tcEnv texp = 
  let (ty, map0) = toTypeAndGetMap [] texp
      ty'        = expandType m tcEnv ty
      texp'      = fromType'' (identSupplyFromMap map0) ty'
  in texp' 
  where
  identSupplyFromMap :: Map.Map Ident Int -> [Ident]
  identSupplyFromMap map' = map snd $ sortBy smaller $ map swap $ Map.toList map'
  swap (x, y) = (y, x)
  smaller (x, _) (x', _) = compare x x'

-- |this is a slightly modified version of fromType' that doesn't convert
-- TypeConstructors that are Lists/Tuples/Unit back into the corresponding
-- TypeExpr type. 
fromType'' :: [Ident] -> Type -> TypeExpr
fromType'' supply (TypeConstructor tc tys) = 
  ConstructorType tc $ map (fromType'' supply) tys
fromType'' supply (TypeVariable tv)         = VariableType
   (if tv >= 0 then supply !! tv else mkIdent ('_' : show (-tv)))
fromType'' supply (TypeConstrained tys _)   = fromType'' supply (head tys)
fromType'' supply (TypeArrow     ty1 ty2)   =
  ArrowType (fromType'' supply ty1) (fromType'' supply ty2)
fromType'' _supply (TypeSkolem          k)   =
  VariableType $ mkIdent $ "_?" ++ show k
fromType'' supply (TypeRecord     fs rty)   = RecordType
  (map (\ (l, ty) -> ([l], fromType'' supply ty)) fs)
  ((fromType'' supply . TypeVariable) `fmap` rty)

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
buildTypeSchemes :: Bool -> ModuleIdent -> TCEnv -> Class -> Class
buildTypeSchemes expand m tcEnv cls@(Class { theClass = tc, methods = ms, typeVar = classTypeVar }) 
  = cls { typeSchemes = typeSchemes', methods = ms' }
  where 
    typeSchemes' = map buildTypeScheme ms
    buildTypeScheme :: (Ident, ST.Context, TypeExpr) -> (Ident, TypeScheme)
    buildTypeScheme (id0, (Context cElems), typeExpr) =
      -- add also the class to the context!
      let extendedCx = Context (ContextElem tc classTypeVar [] : cElems)
          (translatedContext, theType) = toConstrType [classTypeVar] (extendedCx, typeExpr) 
      in (id0, polyType 
            (if expand then expandType m tcEnv theType else expandSpecial theType) 
            `constrainBy` translatedContext)
    typeSchemeToMethod :: (Ident, TypeScheme) -> (Ident, Context, TypeExpr)
    typeSchemeToMethod (m', ForAll _cx _ ty) = 
      (m', {-fromContext' [classTypeVar] cx-}emptyContext, fromType'' [classTypeVar] ty)  
    ms' = map typeSchemeToMethod typeSchemes'

-- |translate the methods to typeschemes, not expanding the types. 
buildTypeSchemesNoExpand :: Class -> Class
buildTypeSchemesNoExpand = buildTypeSchemes False (mkMIdent []) initTCEnv

-- |Only expands special type constructors, i.e., units, tuples and lists. 
-- This is neccessary when we have an already expanded type from the interface;
-- as lists and tuples have special syntactical forms, they are the only elements
-- still unexpanded and have to be expanded. 
expandSpecial :: Type -> Type
expandSpecial v@(TypeVariable _) = v
expandSpecial (TypeConstructor qid tys) 
  | qid == qualify unitId = TypeConstructor (qualify' qid) tys'
  | isQTupleId qid        = TypeConstructor (qualify' qid) tys'
  | qid == qualify listId = TypeConstructor (qualify' qid) tys'
  | otherwise             = TypeConstructor qid tys'
  where tys' = map expandSpecial tys
        qualify' = qualifyWith preludeMIdent . unqualify
expandSpecial (TypeArrow t1 t2) = TypeArrow (expandSpecial t1) (expandSpecial t2)
expandSpecial (TypeConstrained tys n) = TypeConstrained (map expandSpecial tys) n 
expandSpecial ts@(TypeSkolem _) = ts
expandSpecial (TypeRecord ts n) = 
  TypeRecord (map (\(id0, ty) -> (id0, expandSpecial ty)) ts) n

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
  
errNonEmptyContext :: Position -> [Ident] -> Message
errNonEmptyContext p ids = posMessage p $ 
  text "Contexts in type signatures of class methods currently not supported! "
  $$ text "Concerned: The following methods:" <+> text (show ids)  

errNotSupportedDerivingClass :: Position -> Ident -> QualIdent -> Message
errNotSupportedDerivingClass p ty cls = posMessage p $
  text "Cannot derive instance for the type" <+> text (show ty) <+>
  text "and the class" <+> text (show cls)

errEmptyDataTypeDeriving :: Position -> Ident -> Message
errEmptyDataTypeDeriving p ty = posMessage p $ 
  text "Cannot derive an instance for an empty data type (here" <+> text (show ty)
  <> text ")"