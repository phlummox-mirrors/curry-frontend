{- |
    Module      :  $Header$
    Description :  TODO
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Description: TODO
-}

module Checks.TypeClassesCheck (typeClassesCheck) where

import Curry.Syntax.Type as ST hiding (IDecl)
import Env.ClassEnv
import Env.TypeConstructor
import Base.Messages (Message, message, posMessage, internalError)

import Data.List
import Text.PrettyPrint hiding (sep)
import qualified Data.Map as Map
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

-- ---------------------------------------------------------------------------
-- main function
-- ---------------------------------------------------------------------------

-- |Checks class and instance declarations and removes these declarations; 
-- adds new data types/functions for the class and instance declarations. 
-- Also builds a corresponding class environment. 
typeClassesCheck :: ModuleIdent -> [Decl] -> ClassEnv -> TCEnv -> ([Decl], ClassEnv, [Message])
typeClassesCheck m decls (ClassEnv importedClasses importedInstances _) tcEnv = 
  case runTcc result initTccState of 
    ((classes, instances), []) -> 
      let newDecls = concatMap (transformInstance cEnv) $ 
            concatMap (transformClass2 cEnv) decls
          classes' = map renameTypeSigVars classes
          classes'' = map buildTypeSchemes classes'
          cEnv = ClassEnv classes'' instances (buildClassMethodsMap classes'')
      in (newDecls, cEnv, [])
    (_, errs@(_:_)) -> (decls, ClassEnv [] [] Map.empty, errs)
  where
    classDecls = filter isClassDecl decls
    instDecls = filter isInstanceDecl decls
    dataDecls = filter (\x -> isDataDecl x || isNewtypeDecl x) decls
    typeSigs = gatherTypeSigs decls
    allDataTypes = gatherDataTypes dataDecls m
    result = do
      mapM_ typeVariableInContext classDecls
      mapM_ classMethodSigsContainTypeVar classDecls
      mapM_ instanceTypeVarsDoNotAppearTwice instDecls
      
      -- gather all classes and instances for more "global" checks
      let classes = map classDeclToClass classDecls ++ importedClasses
          instances = map instanceDeclToInstance instDecls ++ importedInstances
          newClassEnv = ClassEnv classes instances Map.empty
      -- TODO: check also contexts of (imported) classes and interfaces?
      mapM_ (checkClassesInContext m newClassEnv) classDecls
      mapM_ (checkClassesInContext m newClassEnv) instDecls
      -- check also contexts in typed expressions
      mapM_ (checkClassesInContext m newClassEnv) typeSigs
      
      -- mapM_ checkTypeVarsInContext classDecls -- checked above (typeVariableInContext)
      mapM_ checkTypeVarsInContext instDecls
      mapM_ checkTypeVarsInContext typeSigs 
            
      mapM_ (checkRulesInInstanceOrClass newClassEnv) instDecls
      mapM_ (checkRulesInInstanceOrClass newClassEnv) classDecls
      
      mapM_ (checkClassNameInScope newClassEnv) instDecls
      mapM_ (checkInstanceDataTypeCorrect allDataTypes tcEnv) instDecls
      
      checkForDuplicateClassNames newClassEnv
      checkForDuplicateInstances newClassEnv
      
      checkForCyclesInClassHierarchy newClassEnv
      mapM_ (checkForDirectCycle m) classDecls
      
      mapM_ (checkForInstanceDataTypeExistAlsoInstancesForSuperclasses newClassEnv) instDecls
      mapM_ (checkInstanceContextImpliesAllInstanceContextsOfSuperClasses newClassEnv) instDecls
      
      noDoubleClassMethods classes
      return (classes, instances)

-- |converts a class declaration into the form of the class environment 
classDeclToClass :: Decl -> Class
classDeclToClass (ClassDecl _ (SContext scon) cls tyvar decls) 
  = Class { 
    superClasses = map fst scon, 
    theClass = qualify cls, -- TODO: qualify? 
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
classDeclToClass _ = internalError "classDeclToClass"
  

-- |constructs a map from class methods to their defining classes 
buildClassMethodsMap :: [Class] -> Map.Map QualIdent QualIdent
buildClassMethodsMap cls = Map.unions $ map addClassMethods cls

addClassMethods :: Class -> Map.Map QualIdent QualIdent
addClassMethods (Class { methods = ms, theClass = cls}) = 
  let ms_cls = map (\(m, _, _) -> (qualify m, cls)) ms
  in foldr (uncurry Map.insert) Map.empty ms_cls

-- |converts an instance declaration into the form of the class environment
instanceDeclToInstance :: Decl -> Instance
instanceDeclToInstance (InstanceDecl _ (SContext scon) cls tcon ids decls) = 
  Instance { 
    context = scon, 
    iClass = cls,  
    iType = tyConToQualIdent tcon, 
    typeVars = ids, 
    rules = decls }
instanceDeclToInstance _ = internalError "instanceDeclToInstance"

tyConToQualIdent :: TypeConstructor -> QualIdent
tyConToQualIdent (QualTC qid) = qid
tyConToQualIdent UnitTC = qUnitIdP
tyConToQualIdent (TupleTC n) = qTupleIdP n 
tyConToQualIdent ListTC = qListIdP
tyConToQualIdent ArrowTC = qArrowId

-- |extract all data types/newtypes 
gatherDataTypes :: [Decl] -> ModuleIdent -> [(QualIdent, Int)]
gatherDataTypes decls m = concatMap getDataType decls
  where
  getDataType (DataDecl _ d ids _) = 
    let a = length ids in [(qualify d, a), (qualifyWith m d, a)]
  getDataType (NewtypeDecl _ d ids _) = 
    let a = length ids in [(qualify d, a), (qualifyWith m d, a)]
  getDataType _ = internalError "allDataTypes"

-- |gathers *all* type signatures, also those that are in nested scopes and in
-- classes etc.
gatherTypeSigs :: [Decl] -> [Decl]
gatherTypeSigs decls = 
  -- filter isTypeSig decls ++ 
  concatMap gatherTS decls

gatherTS :: Decl -> [Decl]
gatherTS (ClassDecl _ _ _ _ decls) = gatherTypeSigs decls
gatherTS (InstanceDecl _ _ _ _ _ decls) = gatherTypeSigs decls
gatherTS (PatternDecl _ _ rhs) = gatherTSRhs rhs
gatherTS (FunctionDecl _ _ eqs) = concatMap gatherTSEqu eqs 
gatherTS ts@(TypeSig _ _ _ _) = [ts]
gatherTS _ = []

gatherTSRhs :: Rhs -> [Decl]
gatherTSRhs (SimpleRhs _ expr decls) = gatherTSExpr expr ++ gatherTypeSigs decls
gatherTSRhs (GuardedRhs cexps decls) = concatMap gatherTSCondExpr cexps ++ gatherTypeSigs decls

gatherTSEqu :: Equation -> [Decl]
gatherTSEqu (Equation _ _ rhs) = gatherTSRhs rhs

gatherTSExpr :: Expression -> [Decl]
gatherTSExpr (Literal _) = []
gatherTSExpr (Variable _) = []
gatherTSExpr (Constructor _) = []
gatherTSExpr (Paren expr) = gatherTSExpr expr
-- convert typification into type signatures without position (TODO: add
-- position somehow)
gatherTSExpr (Typed expr cx texp) = gatherTSExpr expr ++ [TypeSig NoPos [] cx texp]
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
-- in scope  
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
  case lookupClass cEnv (qualUnqualify m qid) of 
    Nothing -> report (errClassNotInScope p qid)
    Just _ -> ok

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
noDoubleClassMethods :: [Class] -> Tcc ()
noDoubleClassMethods classes = 
  let allMethods = map fst3 $ concatMap (\(Class {methods=ms}) -> ms) classes
      theNub = nub allMethods -- nubBy (\ms1 ms2 -> fst3 ms1 == fst3 ms2) allMethods
  in if length theNub /= length allMethods
  then report (errDoubleClassMethods NoPos NoPos (allMethods \\ theNub))
  else ok

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
    isDefinedFunctionClassMethod (cls, FunctionDecl p f _) 
      = let ms = methods (fromJust $ lookupClass cEnv cls)
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
  else report 
        (errCyclesInClassHierarchy $ head $ filter (\xs -> length xs > 1) sccs)
  where 
    sccs = scc (\qid -> [qid]) 
               (\qid -> (superClasses $ fromJust $ lookupClass cEnv qid))
               (map theClass classes)

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
checkForDuplicateClassNames :: ClassEnv -> Tcc ()
checkForDuplicateClassNames (ClassEnv classes _ _) = 
  let duplClassNames = findMultiples $ map theClass classes
  in if null duplClassNames
  then ok
  else report (errDuplicateClassNames (map head duplClassNames)) 


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

-- |Checks whether the class name in an instance definition is in scope
checkClassNameInScope :: ClassEnv -> Decl -> Tcc ()
checkClassNameInScope cEnv (InstanceDecl p _ cls _ _ _) = 
  if isNothing $ lookupClass cEnv cls 
  then report (errClassNameNotInScope p cls)
  else ok
checkClassNameInScope _ _ = internalError "checkClassNameInScope"

-- |Checks whether the instance data type is in scope and not a type synonym. 
-- Check also that the arity of the data type in the instance declaration
-- is correct. 
checkInstanceDataTypeCorrect :: [(QualIdent, Int)] -> TCEnv -> Decl -> Tcc ()
checkInstanceDataTypeCorrect dataTypes tcEnv (InstanceDecl p _ _ (QualTC qid) ids _) =
  -- if the data type is defined in the module and in the type constructor
  -- environment or more than once in the type constructor environment -> error! 
  if (defInModule && defInTCEnv) || length tinfo > 1
  then report (errDataTypeAmbiguous p qid)
  -- check if data type is defined in this module
  else if defInModule
  then if arity == length ids
       then ok
       else report (errDataTypeHasIncorrectArity p qid)
  -- if data type is not defined in this module, search it in the type
  -- constructor environment that contains all imported type constructors
  else if defInTCEnv
  then if tcArity (head tinfo) /= length ids
            then report (errDataTypeHasIncorrectArity p qid)
            else ok
  else report (errDataTypeNotInScope p qid) 

  where arity = fromJust $ lookup qid dataTypes
        tinfo = qualLookupTC qid tcEnv 
        defInModule = qid `elem` (map fst dataTypes)
        defInTCEnv = not . null $ tinfo
checkInstanceDataTypeCorrect _dataTypes _ (InstanceDecl _ _ _ _ _ _) = ok
checkInstanceDataTypeCorrect _ _ _ = internalError "checkInstanceDataTypeCorrect"

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
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses :: ClassEnv -> Decl -> Tcc ()
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses cEnv 
    (InstanceDecl p _scon cls ty _tyvars _)
  = let -- TODO: is it sufficient to take only direct superclasses? 
        -- scs = superClasses (fromJust $ lookupClass cEnv cls)
        scs = allSuperClasses cEnv cls
        tyId = tyConToQualIdent ty
        insts = map (\c -> getInstance cEnv c tyId) scs 
        missingInsts = map fst $ filter (isNothing . snd) $ zip scs insts in
    unless (all isJust insts) $ report $ 
      errMissingSuperClassInstances p ty missingInsts      
checkForInstanceDataTypeExistAlsoInstancesForSuperclasses _ _ 
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
    ClassEnv -> Decl -> Tcc ()
checkInstanceContextImpliesAllInstanceContextsOfSuperClasses cEnv
    inst@(InstanceDecl p _scon cls ty tyvars _)
  = let thisContext = getContextFromInstDecl inst
        scs = allSuperClasses cEnv cls
        tyId = tyConToQualIdent ty
        insts = map fromJust $ filter isJust $ map (\c -> getInstance cEnv c tyId) scs
        instCxs = concatMap getContextFromInst insts
        
        thisContext' = getSContextFromContext thisContext tyvars
        instCxs' = getSContextFromContext instCxs tyvars
        notImplCxs = (filter (not . implies cEnv thisContext) instCxs)
        notImplCxs' = getSContextFromContext notImplCxs tyvars in
    unless (implies' cEnv thisContext instCxs) $ report $  
      errContextNotImplied p thisContext' instCxs' notImplCxs'
        
checkInstanceContextImpliesAllInstanceContextsOfSuperClasses _ _
  = internalError "checkInstanceContextImpliesAllInstanceContextsOfSuperClasses"

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
  -- TODO: qualify/unqualify??
  theSuperClasses = 
    map (show . unqualify) $ 
      superClasses theClass0
  qSuperClasses = map (dictTypePrefix ++) theSuperClasses
  scs = map (\s -> ConstructorType (qualify $ mkIdent s) [VariableType tyvar])
    qSuperClasses
  methodTypes = map third theMethods0
  genSuperClassDictSelMethod :: String -> [Decl]
  genSuperClassDictSelMethod scls = 
    let selMethodId = mkIdent $ selMethodName
        selMethodName = selFunPrefix ++ (show $ theClass theClass0) ++ sep ++ scls in
    [ TypeSig NoPos [selMethodId]
        emptyContext (ArrowType 
          (ConstructorType (qualify $ dataTypeName) [VariableType tyvar]) 
          (ConstructorType (qualify $ mkIdent $ dictTypePrefix ++ scls) [VariableType tyvar]))
    , FunctionDecl NoPos selMethodId 
       [Equation NoPos 
         (equationsLhs selMethodName)
         (SimpleRhs NoPos (Variable $ qualify $ dictSelParam selMethodName scls) [])
       ]
    ]
  genMethodSelMethod :: ((Ident, Context, TypeExpr), Int) -> [Decl]
  genMethodSelMethod ((m, _cx, ty), i) = 
    let selMethodId = mkIdent $ selMethodName
        selMethodName = selFunPrefix ++ (show $ theClass theClass0) ++ sep ++ (show m) in
    [ TypeSig NoPos [selMethodId]
        emptyContext (ArrowType 
          (ConstructorType (qualify $ mkIdent $ dictTypePrefix ++ (show cls)) [VariableType tyvar]) 
          ty)
    , FunctionDecl NoPos selMethodId 
       [Equation NoPos 
         (equationsLhs selMethodName)
         (SimpleRhs NoPos (Variable $ qualify $ methodSelParam selMethodName i) [])
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
    mkIdent (selMethodName ++ sep ++ s)
  methodSelParam selMethodName n = flip renameIdent 1 $ 
    mkIdent (selMethodName ++ sep ++ "x" ++ (show n))
  
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
  -- TODO: unqualify???
  superClasses0 = map (show {-. unqualify-}) $ superClasses theClass0
  superClasses1 = superClasses theClass0
  methods0 = methods theClass0
  nonDirectSuperClasses = allSuperClasses cEnv (theClass theClass0) \\ superClasses1
  
  -- | Generates functions for extracting (direct) super class dictionaries 
  -- from a given dictionary
  genSuperClassDictSelMethod :: String -> [Decl]
  genSuperClassDictSelMethod scls = 
    let selMethodName = selFunPrefix ++ (show $ theClass theClass0) ++ sep ++ scls in
    [ FunctionDecl NoPos (mkIdent selMethodName)
      [Equation NoPos
        (equationLhs selMethodName)
        (SimpleRhs NoPos (Variable $ qualify $ dictSelParam selMethodName scls) [])
      ]
    ]
    
  -- | Generates functions for extracting the class functions from a given 
  -- directory 
  genMethodSelMethod :: ((Ident, Context, TypeExpr), Int) -> [Decl]
  genMethodSelMethod ((m, _cx, _ty), i) = 
    let selMethodName = selFunPrefix ++ (show $ theClass theClass0) ++ sep ++ (show m) in
    [ FunctionDecl NoPos (mkIdent selMethodName)
      [Equation NoPos
        (equationLhs selMethodName)
        (SimpleRhs NoPos (Variable $ qualify $ methodSelParam selMethodName i) [])
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
    let selMethodName = selFunPrefix ++ (show $ theClass theClass0) ++ sep ++ (show scls) in
    [ FunctionDecl NoPos (mkIdent selMethodName)
      [Equation NoPos
        (FunLhs (mkIdent selMethodName) [])
        (SimpleRhs NoPos expr [])
      ]
    ]
    where
    -- we want the shortest path in the superclass hierarchy to the given 
    -- superclass
    path = fromJust $ findPath cEnv (theClass theClass0) scls 
    -- generate the names of the selector functions 
    names :: [QualIdent] -> [Expression]
    names (x:y:zs) = 
      (Variable $ qualify $ mkIdent $ selFunPrefix ++ (show x) ++ sep ++ (show y)) 
      : names (y:zs)
    names [_] = []
    names [] = internalError "genNonDirectSuperClassDictSelMethod"
    -- enchain the selector functions
    expr :: Expression
    expr = foldr1 (\e1 e2 -> InfixApply e1 (InfixOp point) e2) (reverse $ names path)
    point = qualify $ mkIdent "."
    
  -- the renamings are important so that the parameters are not handled as
  -- global functions. Also important is that the parameters are globally
  -- unique
  dictSelParam selMethodName s = flip renameIdent 1 $ 
    mkIdent (selMethodName ++ sep ++ s)
  methodSelParam selMethodName n = flip renameIdent 1 $ 
    mkIdent (selMethodName ++ sep ++ "x" ++ (show n))
  
  
transformClass2 _ d = [d]

-- |The prefix for dictionary types
dictTypePrefix :: String
dictTypePrefix = "Dict" ++ sep

-- |The prefix for dictionaries
dictPrefix :: String
dictPrefix = "dict" ++ sep

-- |The prefix for selector functions
selFunPrefix :: String
selFunPrefix = "sel" ++ sep

-- |The prefix for functions that are implemented in a given instance declaration
implPrefix :: String
implPrefix = "impl" ++ sep

sep :: String
sep = "."

type IDecl = Decl

-- |transformInstance creates top level functions for the methods 
-- of which rules are given in the instance declaration, and concrete 
-- dictionaries, as well as type signatures for the instance rules. 
transformInstance :: ClassEnv -> IDecl -> [Decl]
transformInstance cEnv idecl@(InstanceDecl _ _ cls _ _ decls)
  = concatMap (transformMethod cEnv idecl) decls
  ++ concatMap (handleMissingFunc cEnv idecl) missingMethods
  -- create dictionary 
  ++ createDictionary2 cEnv idecl
  where
  presentMethods = nub $ map (\(FunctionDecl _ id0 _) -> id0) decls
  theClass0 = fromJust $ lookupClass cEnv cls 
  theMethods0 = nub $ map fst3 $ methods theClass0
  missingMethods = theMethods0 \\ presentMethods
transformInstance _ d = [d]

-- |transforms one method defined in an instance to a top level function 
transformMethod :: ClassEnv -> IDecl -> Decl -> [Decl]
transformMethod cEnv idecl@(InstanceDecl _ _ cls tcon _ _)
                      decl@(FunctionDecl _ _ _) =
  -- create type signature
  createTypeSignature rfunc cEnv idecl decl
  -- create function rules
  : [createTopLevelFuncs rfunc decl] 
  where 
    -- rename for specific instance!
    rfunc = (\s -> instMethodName cls tcon s)
transformMethod _ _ _ = internalError "transformMethod"

-- |create a name for the (hidden) function that is implemented by the  
-- function definitions in the instance  
instMethodName :: QualIdent -> TypeConstructor -> String -> String
instMethodName cls tcon s = implPrefix ++ show cls ++ sep ++ show tcon ++ sep ++ s

-- |creates a type signature for an instance method which is transformed to
-- a top level function
createTypeSignature :: RenameFunc -> ClassEnv -> IDecl -> Decl -> Decl
createTypeSignature rfunc cEnv (InstanceDecl _ scx cls tcon tyvars _) 
                    (FunctionDecl p f _eqs) 
  = TypeSig p [rename rfunc f] cx' ty'
  where 
    -- lookup class method of f
    theClass_ = fromJust $ lookupClass cEnv cls
    (_, cx, ty) = fromJust $ find (\(id0, _, _) -> id0 == f) (methods theClass_)
    
    -- Substitute class typevar with given instance type. 
    -- Rename tyvars, so that they do not equal type vars in the class
    -- method type signature, like in the following example:
    -- class C a where fun :: a -> b -> Bool
    -- instance Eq b => C (S b) where fun = ...
    theType = SpecialConstructorType tcon (map (VariableType . flip renameIdent 1) tyvars)
    
    subst = [(typeVar theClass_, theType)]
    -- cx' = substInContext subst cx
    ty' = substInTypeExpr subst ty 
    
    -- add instance context. The variables have to be renamed here as well
    renamedSContext = (\(SContext elems) -> 
      SContext $ map (\(qid, id0) -> (qid, renameIdent id0 1)) elems) scx
    icx = simpleContextToContext renamedSContext
    cx' = combineContexts icx cx
createTypeSignature _ _ _ _ = internalError "createTypeSignature"    
      

combineContexts :: ST.Context -> ST.Context -> ST.Context
combineContexts (Context e1) (Context e2) = Context (e1 ++ e2)

type RenameFunc = String -> String

createTopLevelFuncs :: RenameFunc -> Decl -> Decl
createTopLevelFuncs rfunc (FunctionDecl p id0 eqs) 
  = FunctionDecl p (rename rfunc id0) (map (transEq rfunc) eqs)
createTopLevelFuncs _ _ = internalError "createTopLevelFuncs"
  
transEq :: RenameFunc -> Equation -> Equation
transEq rfunc (Equation p lhs rhs) = Equation p (transLhs rfunc lhs) rhs

transLhs :: RenameFunc -> Lhs -> Lhs
transLhs rfunc (FunLhs id0 ps) = FunLhs (rename rfunc id0) ps
transLhs rfunc (OpLhs ps1 id0 ps2) = OpLhs ps1 (rename rfunc id0) ps2
transLhs rfunc (ApLhs lhs ps) = ApLhs (transLhs rfunc lhs) ps

rename :: RenameFunc -> Ident -> Ident
rename rfunc = updIdentName rfunc  

-- |handles functions missing in an instance declaration. Searches for a
-- default method (TODO!) and inserts this, else inserts an error statement
handleMissingFunc :: ClassEnv -> IDecl -> Ident -> [Decl]
handleMissingFunc _cEnv (InstanceDecl _ _ cls ty _ _) fun = 
  [ FunctionDecl NoPos globalName [if defaultMethodDefined then equ2 else equ1]
  ]
  where
  globalName = mkIdent $ instMethodName cls ty (show fun)
  equ1 = Equation NoPos (FunLhs globalName []) 
    (SimpleRhs NoPos (Apply (Variable . qualify . mkIdent $ "error") 
                            (Literal $ String (srcRef 0) errorString)) [])
  errorString = show fun ++ " not given in instance declaration of class "
    ++ show cls ++ " and type " ++ show ty
  equ2 = undefined -- TODO
  defaultMethodDefined = False -- TODO
handleMissingFunc _ _ _ = internalError "handleMissingFunc"

-- |This function creates a dictionary for the given instance declaration, 
-- using dictionary data types instead of tuples
createDictionary :: ClassEnv -> IDecl -> [Decl]
createDictionary cEnv (InstanceDecl _ _scx cls ty _tvars _decls) = 
  [ FunctionDecl NoPos (dictName cls)
    [Equation NoPos
      (FunLhs (dictName cls) [])
      (SimpleRhs NoPos 
        all' [])
      ]
  ] 
  where
  dictName c = mkIdent $ dictPrefix ++ (show c) ++ sep ++ (show ty)
  theClass0 = fromJust $ lookupClass cEnv cls
  superClasses0 = superClasses theClass0
  methods0 = methods theClass0
  scs = map (Variable . qualify . dictName) superClasses0
  ms = map (Variable . qualify . mkIdent . 
    (\s -> instMethodName cls ty s) . show . fst3) methods0
  all0 = scs ++ ms
  dict = qualify $ mkIdent $ dictTypePrefix ++ show cls
  all' = foldl Apply (Constructor dict) all0
createDictionary _ _ = internalError "createDictionary"

-- |This function creates a dictionary for the given instance declaration, 
-- using tuples
createDictionary2 :: ClassEnv -> IDecl -> [Decl]
createDictionary2 cEnv (InstanceDecl _ _scx cls ty _tvars _decls) = 
  [ FunctionDecl NoPos (dictName cls)
    [Equation NoPos
      (FunLhs (dictName cls) [])
      (SimpleRhs NoPos 
        (if length all0 == 1 then head all0 else Tuple noRef all0) [])
      ]
  ] 
  where
  dictName c = mkIdent $ dictPrefix ++ (show c) ++ sep ++ (show ty)
  theClass0 = fromJust $ lookupClass cEnv cls
  superClasses0 = superClasses theClass0
  methods0 = methods theClass0
  scs = map (Variable . qualify . dictName) superClasses0
  ms = map (Variable . qualify . mkIdent . 
    (\s -> instMethodName cls ty s) . show . fst3) methods0
  all0 = scs ++ ms
createDictionary2 _ _ = internalError "createDictionary"
 
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
buildTypeSchemes :: Class -> Class
buildTypeSchemes cls@(Class { theClass = tc, methods = ms, typeVar = classTypeVar }) 
  = cls { typeSchemes = map buildTypeScheme ms }
  where 
    buildTypeScheme :: (Ident, ST.Context, TypeExpr) -> (Ident, TypeScheme)
    buildTypeScheme (id0, (Context cElems), typeExpr) =
      -- add also the class to the context!
      let extendedCx = Context (ContextElem tc classTypeVar [] : cElems)
          (translatedContext, theType) = toConstrType [classTypeVar] (extendedCx, typeExpr) 
      in (id0, (polyType theType `constrainBy` translatedContext))



-- ---------------------------------------------------------------------------
-- various substitutions
-- ---------------------------------------------------------------------------

type Subst a = [(Ident, a)]

applySubst :: (Subst Ident) -> Ident -> Ident
applySubst subst id0 = case lookup id0 subst of
  Nothing -> id0
  Just x -> x

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

errDuplicateClassNames :: [QualIdent] -> Message
errDuplicateClassNames clss 
  = message (text "Two or more classes with the same name: "  
  <+> hsep (punctuate comma (map ppQIdent clss)))
  
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

