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

import Curry.Syntax.Type
import Env.ClassEnv
import Base.Messages (Message, {-message, -}posMessage, internalError)

import Data.List
import Text.PrettyPrint
import qualified Data.Map as Map

-- import Base.Types (Type (..), TypeScheme (..))
import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax.Utils

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
      (decls {-_rest2-}, ClassEnv classes instances (buildClassMethodsMap classes), [])
    CheckFailed errs -> (decls, ClassEnv [] [] Map.empty, errs)
  where
    (classDecls, rest1) = partition isClassDecl decls
    (instDecls, _rest2)  = partition isInstanceDecl rest1
    result = do
      mapM_ typeVariableInContext classDecls
      -- gather all classes and instances for more "global" checks
      let classes = map classDeclToClass classDecls ++ importedClasses
      let instances = map instanceDeclToInstance instDecls ++ importedInstances
      let newClassEnv = ClassEnv classes instances Map.empty
      -- TODO: check also contexts of (imported) classes and interfaces?
      mapM_ (checkSuperclassContext newClassEnv) classDecls
      mapM_ (checkSuperclassContext newClassEnv) instDecls
      return (classes, instances)

-- |converts a class declaration into the form of the class environment 
classDeclToClass :: Decl -> Class
classDeclToClass (ClassDecl _ (SContext scon) cls tyvar decls) 
  = Class { 
    superClasses = map fst scon, 
    theClass = qualify cls, -- TODO: qualify? 
    typeVar = tyvar, 
    kind = -1, -- TODO
    methods = map (\(TypeSig _ [id0] cx ty) -> (id0, cx, ty)) $ 
      concatMap splitUpTypeSig $ filter isTypeSig decls, 
    defaults = filter isFunctionDecl decls
  }
  where
    splitUpTypeSig :: Decl -> [Decl]
    splitUpTypeSig (TypeSig p ids cx ty) 
      = map (\id0 -> TypeSig p [id0] cx ty) ids
    splitUpTypeSig _ = internalError "splitUpTypeSig"
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