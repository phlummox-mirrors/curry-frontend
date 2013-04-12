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
import Base.Messages (Message, posMessage, internalError)

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

typeClassesCheck :: [Decl] -> ClassEnv -> ([Decl], ClassEnv, [Message])
typeClassesCheck decls _cenv = 
  case result of 
    CheckSuccess (classes, instances) -> 
      (decls {-_rest2-}, ClassEnv classes instances (buildClassMethodsMap classes), [])
    CheckFailed errs -> (decls, ClassEnv [] [] Map.empty, errs)
  where
    (classDecls, rest1) = partition isClassDecl decls
    (instDecls, _rest2)  = partition isInstanceDecl rest1
    result = do
      mapM_ typeVariableInContext classDecls
      let classes = map classDeclToClass classDecls
      let instances = map instanceDeclToInstance instDecls
      return (classes, instances)
        
classDeclToClass :: Decl -> Class
classDeclToClass (ClassDecl _ (SContext scon) cls tyvar decls) 
  = Class { 
    superClasses = map fst scon, 
    theClass = cls, 
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
  

buildClassMethodsMap :: [Class] -> Map.Map QualIdent QualIdent
buildClassMethodsMap cls = Map.unions $ map addClassMethods cls

addClassMethods :: Class -> Map.Map QualIdent QualIdent
addClassMethods (Class { methods = ms, theClass = cls}) = 
  let ms_cls = map (\(m, _, _) -> (qualify m, qualify cls)) ms
  in foldr (uncurry Map.insert) Map.empty ms_cls
  
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

typeVariableInContext :: Decl -> CheckResult ()
typeVariableInContext (ClassDecl p (SContext scon) _cls tyvar _decls) 
 = let idsInContext = map snd scon in 
   if not (null scon) && nub idsInContext /= [tyvar]
   then CheckFailed [errTypeVariableInContext p (nub idsInContext \\ [tyvar])]
   else return ()
typeVariableInContext _ = internalError "typeVariableInContext"


errTypeVariableInContext :: Position -> [Ident] -> Message
errTypeVariableInContext p ids 
  = posMessage p 
  (text "Illegal type variable(s)" <+> text (show ids) 
   <+> text "in class context")
  
 