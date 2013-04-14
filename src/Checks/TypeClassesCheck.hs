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

import Curry.Syntax.Type as ST
import Env.ClassEnv
import Base.Messages (Message, message, posMessage, internalError)

import Data.List
import Text.PrettyPrint
import qualified Data.Map as Map
import Data.Maybe

-- import Base.Types (Type (..), TypeScheme (..))
import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax.Utils
import Curry.Syntax.Pretty
import Base.CurryTypes
import Base.Types as BT (TypeScheme, polyType, Context, Type (..), constrainBy) 

data CheckResult a
  = CheckSuccess a
  | CheckFailed [Message]

instance Monad CheckResult where
  return = CheckSuccess
  (>>=)  = thenCheck

thenCheck :: CheckResult a -> (a -> CheckResult b) -> CheckResult b
thenCheck chk cont = case chk of
  CheckSuccess   a -> cont a
  CheckFailed errs -> CheckFailed errs

-- ---------------------------------------------------------------------------
-- main function
-- ---------------------------------------------------------------------------

-- |Checks class and instance declarations. TODO: removes these declarations?
-- Builds a corresponding class environment 
typeClassesCheck :: [Decl] -> ClassEnv -> ([Decl], ClassEnv, [Message])
typeClassesCheck decls (ClassEnv importedClasses importedInstances _) = 
  case result of 
    CheckSuccess (classes, instances) -> 
      let newDecls = concatMap transformInstances $ concatMap transformClasses decls
          classes' = map renameTypeSigVars classes
          classes'' = map buildTypeSchemes classes'
      in (newDecls, ClassEnv classes'' instances (buildClassMethodsMap classes''), [])
    CheckFailed errs -> (decls, ClassEnv [] [] Map.empty, errs)
  where
    (classDecls, rest1) = partition isClassDecl decls
    (instDecls, _rest2)  = partition isInstanceDecl rest1
    result = do
      mapM_ typeVariableInContext classDecls
      mapM_ classMethodSigsContainTypeVar classDecls
      
      -- gather all classes and instances for more "global" checks
      let classes = map classDeclToClass classDecls ++ importedClasses
      let instances = map instanceDeclToInstance instDecls ++ importedInstances
      let newClassEnv = ClassEnv classes instances Map.empty
      -- TODO: check also contexts of (imported) classes and interfaces?
      mapM_ (checkSuperclassContext newClassEnv) classDecls
      mapM_ (checkSuperclassContext newClassEnv) instDecls
      
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
    iType = tcon, 
    typeVars = ids, 
    rules = decls }
instanceDeclToInstance _ = internalError "instanceDeclToInstance"

-- ---------------------------------------------------------------------------
-- checks
-- ---------------------------------------------------------------------------

-- |check that in classes the type variables in the context are exactly the
-- one that is given after the class name
-- legal: Eq a => Ord a
-- illegal: Eq b => Ord a  
typeVariableInContext :: Decl -> CheckResult ()
typeVariableInContext (ClassDecl p (SContext scon) _cls tyvar _decls) 
 = let idsInContext = map snd scon in 
   if not (null scon) && nub idsInContext /= [tyvar]
   then CheckFailed [errTypeVariableInContext p (nub idsInContext \\ [tyvar])]
   else return ()
typeVariableInContext _ = internalError "typeVariableInContext"

-- |check that the classes in superclass contexts or instance contexts are 
-- in scope  
checkSuperclassContext :: ClassEnv -> Decl -> CheckResult ()
checkSuperclassContext cEnv (ClassDecl p (SContext scon) _ _ _) = 
  mapM_ (checkSuperclassContext' cEnv p) (map fst scon)
checkSuperclassContext cEnv (InstanceDecl p (SContext scon) _ _ _ _) = 
  mapM_ (checkSuperclassContext' cEnv p) (map fst scon)
checkSuperclassContext _ _ = internalError "TypeClassesCheck.checkSuperclassContext"
    
checkSuperclassContext' :: ClassEnv -> Position -> QualIdent -> CheckResult ()
checkSuperclassContext' cEnv p qid = 
  case lookupClass cEnv qid of 
    Nothing -> CheckFailed [errSuperclassNotInScope p qid]
    Just _ -> return ()

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
noDoubleClassMethods :: [Class] -> CheckResult ()
noDoubleClassMethods classes = 
  let allMethods = map fst3 $ concatMap (\(Class {methods=ms}) -> ms) classes
      theNub = nub allMethods -- nubBy (\ms1 ms2 -> fst3 ms1 == fst3 ms2) allMethods
  in if length theNub /= length allMethods
  then CheckFailed [errDoubleClassMethods NoPos NoPos (allMethods \\ theNub)]
  else return ()
  where fst3 (x, _, _) = x

-- noConflictOfClassMethodsWithTopLevelBinding :: [Class] -> ValueEnv -> CheckResult ()
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
classMethodSigsContainTypeVar :: Decl -> CheckResult ()
classMethodSigsContainTypeVar (ClassDecl _p _scon _tycon tyvar0 decls)
  = mapM_ (tyVarInTypeSig tyvar0) typeSigs
  where 
    typeSigs = filter isTypeSig decls
    tyVarInTypeSig tyvar (TypeSig p ids _con typeExpr) 
      = if tyvar `elem` typeVarsInTypeExpr typeExpr
        then return ()
        else CheckFailed [errTypeVarNotInMethodSig p tyvar ids]
    tyVarInTypeSig _ _ = internalError "TypeClassesCheck tyVarInTypeSig"
classMethodSigsContainTypeVar _ = internalError "TypeClassesCheck" 

-- ---------------------------------------------------------------------------
-- source code transformation
-- ---------------------------------------------------------------------------

transformClasses :: Decl -> [Decl]
transformClasses (ClassDecl p scx cls tyvar decls) = []
transformClasses d = [d]

transformInstances :: Decl -> [Decl]
transformInstances (InstanceDecl p scx cls tcon tyvars decls) = []
transformInstances d = [d]

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

type Subst = [(Ident, Ident)]

buildSubst :: Ident -> [Ident] -> Int -> Subst
buildSubst classTyvar ids n = map 
  (\id0 -> if id0 == classTyvar then (id0, id0)
           else (id0, updIdentName (\i -> i ++ show n) id0))
  ids

applySubst :: Subst -> Ident -> Ident
applySubst subst id0 = case lookup id0 subst of
  Nothing -> id0
  Just x -> x

renameVarsInContext :: Subst -> ST.Context -> ST.Context
renameVarsInContext subst (Context elems) = 
  Context $ map (renameVarsInContextElem subst) elems

renameVarsInContextElem :: Subst -> ContextElem -> ContextElem
renameVarsInContextElem subst (ContextElem qid i texps)
  = ContextElem qid (applySubst subst i) (map (renameVarsInTypeExpr subst) texps)

renameVarsInTypeExpr :: Subst -> TypeExpr -> TypeExpr
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
          (theType, theMap) = toTypeAndGetMap [classTypeVar] typeExpr
          translatedContext = translateContext theMap extendedCx
      in (id0, (polyType theType `constrainBy`translatedContext))

translateContext :: Map.Map Ident Int -> ST.Context -> BT.Context
translateContext theMap (Context elems) 
  -- TODO: translate also texps!
  = map (\(ContextElem qid id0 texps) -> 
         (qid, TypeVariable (fromJust $ Map.lookup id0 theMap)))
        elems

-- ---------------------------------------------------------------------------
-- error messages
-- ---------------------------------------------------------------------------

errTypeVariableInContext :: Position -> [Ident] -> Message
errTypeVariableInContext p ids 
  = posMessage p 
  (text "Illegal type variable(s)" <+> text (show ids) 
   <+> text "in class context")
  
errSuperclassNotInScope :: Position -> QualIdent -> Message
errSuperclassNotInScope p qid = 
  posMessage p (text "superclass" <+> text (show qid)
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
