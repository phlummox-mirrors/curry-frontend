{- |
    Module      :  $Header$
    Description :  Environment for type classes
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This file contains the environment definitions for type classes. 
-}


module Env.ClassEnv 
  ( ClassEnv (..), Class (..), Instance (..), initClassEnv, lookupClass
  , lookupDefiningClass, lookupMethodTypeScheme, lookupMethodTypeSig
  , ppClasses, getAllClassMethods, allSuperClasses, isSuperClassOf
  , allSuperClasses', isSuperClassOf', implies, implies'
  , getInstance, isValidCx, reduceContext
  ) where

-- import Base.Types hiding ()
import Curry.Base.Ident
import Text.PrettyPrint
import Curry.Syntax.Type
import qualified Data.Map as Map
import Curry.Syntax.Pretty
import Control.Monad (liftM)
import Base.Types hiding (Context, typeVar, typeVars)
import qualified Base.Types as BT 
import Data.List
import Data.Maybe
import Base.Messages

-- |The class environment consists of the classes and instances in scope
-- plus a map from class methods to their defining classes
data ClassEnv = ClassEnv 
  { theClasses :: [Class]
  , theInstances :: [Instance] 
  , classMethods :: (Map.Map QualIdent QualIdent)
  } 
  deriving Show

data Class = Class
  { superClasses :: [QualIdent]
  , theClass :: QualIdent -- TODO Ident or QualIdent? 
  , typeVar :: Ident
  , kind :: Int
  , methods :: [(Ident, Context, TypeExpr)]
  , typeSchemes :: [(Ident, TypeScheme)] 
  , defaults :: [Decl]
  }
  deriving (Eq, Show)

data Instance = Instance
  { context :: [(QualIdent,Ident)]
  , iClass :: QualIdent
  , iType :: QualIdent
  , typeVars :: [Ident]
  , rules :: [Decl]
  }
  deriving (Eq, Show)
  
initClassEnv :: ClassEnv 
initClassEnv = ClassEnv [] [] Map.empty

-- |looks up a given class from the class environment
lookupClass :: ClassEnv -> QualIdent -> Maybe Class
lookupClass (ClassEnv cls _ _) c = lookupClass' cls
  where lookupClass' [] = Nothing
        lookupClass' (c'@Class {theClass=tc}:cs) 
          | tc == c = Just c'
          | otherwise = lookupClass' cs

-- |looks up the class that defines the given class method
lookupDefiningClass :: ClassEnv -> QualIdent -> Maybe QualIdent
lookupDefiningClass (ClassEnv _ _ ms) m = Map.lookup m ms  

-- |looks up the type scheme of a given class method
lookupMethodTypeScheme :: ClassEnv -> QualIdent -> Maybe TypeScheme
lookupMethodTypeScheme cEnv qid = do
  theClass_ <- lookupDefiningClass cEnv qid
  classMethods0 <- liftM typeSchemes (lookupClass cEnv theClass_) 
  lookup (unqualify qid) classMethods0  

-- |looks up the method type signature of a given class method
lookupMethodTypeSig :: ClassEnv -> QualIdent -> Maybe (Context, TypeExpr)
lookupMethodTypeSig cEnv qid = do
  theClass_ <- lookupDefiningClass cEnv qid
  classMethods0 <- liftM methods (lookupClass cEnv theClass_)
  lookup3 (unqualify qid) classMethods0

lookup3 :: Eq a => a -> [(a, b, c)] -> Maybe (b, c)
lookup3 _ [] =  Nothing
lookup3 x ((a, b, c):ys) | x == a = Just (b, c)
                         | otherwise = lookup3 x ys

-- |get all type signatures of all methods in all classes 
-- in the given class environment; the context of a given method
-- is expanded by the class itself and for the type variable of 
-- the class. 
getAllClassMethods :: ClassEnv -> [(Ident, Context, TypeExpr)]
getAllClassMethods (ClassEnv classes _ _) = 
  let msAndCls  = map (\c -> (theClass c, typeVar c, methods c)) classes
      msAndCls' = concatMap (\(tc, tyvar, ms_) -> map (\m -> (tc, tyvar, m)) ms_) msAndCls 
      ms        = map (\(tc, tyvar, (id0, cx, ty)) -> (id0, addClassContext tc tyvar cx, ty)) msAndCls'  
  in ms
  where 
    addClassContext :: QualIdent -> Ident -> Context -> Context
    addClassContext cls tyvar (Context elems) 
      = Context (elems ++ [ContextElem cls tyvar []])  
  

-- |returns *all* superclasses of a given class
allSuperClasses :: ClassEnv -> Class -> [QualIdent]
allSuperClasses cEnv c = let scs = superClasses c in 
  nub $ scs 
    ++ concatMap (allSuperClasses cEnv . fromJust . lookupClass cEnv) scs

allSuperClasses' :: ClassEnv -> QualIdent -> [QualIdent]
allSuperClasses' cEnv c = let
  theClass0 = lookupClass cEnv c
  scs = maybe (internalError ("allSuperClasses': " ++ show c)) superClasses theClass0 in
  nub $ scs ++ concatMap (allSuperClasses' cEnv) scs
  
-- |checks whether a given class is a superclass of another class
isSuperClassOf :: ClassEnv -> Class -> Class -> Bool
isSuperClassOf cEnv c1 c2 = (theClass c1) `elem` allSuperClasses cEnv c2

isSuperClassOf' :: ClassEnv -> QualIdent -> QualIdent -> Bool
isSuperClassOf' cEnv c1 c2 = c1 `elem` allSuperClasses' cEnv c2

-- |does a specific context imply a given type assertion?
implies :: ClassEnv -> BT.Context -> (QualIdent, Type) -> Bool
implies cEnv cx (qid, ty) = 
  any (\(qid', ty') -> ty == ty' && (qid == qid' || isSuperClassOf' cEnv qid qid')) cx
  ||
  ((isTyCons ty || isArrow ty) && 
    let (xi, tys) = getTyCons ty
        insts = getInstancesForType cEnv xi in
    any (\i -> 
      let cx' = context i
          ids = typeVars i
          s = zip ids tys
          cx'' = substContext s cx' in
      null (isValidCx cEnv cx'') && implies' cEnv cx cx'') insts)

-- |does a specific context imply another?
implies' :: ClassEnv -> BT.Context -> BT.Context -> Bool
implies' cEnv cx cx' = 
  all (\c' -> implies cEnv cx c') cx' 

-- |get all instances for a given type
getInstancesForType :: ClassEnv -> QualIdent -> [Instance]
getInstancesForType cEnv qid = filter (\inst -> iType inst == qid) (theInstances cEnv)

-- |helper function
substContext :: [(Ident, Type)] -> [(QualIdent, Ident)] -> BT.Context
substContext subst cx = map (\(qid, id0) -> (qid, fromJust $ lookup id0 subst)) cx

getTyCons :: Type -> (QualIdent, [Type])
getTyCons (TypeConstructor xi tys) = (xi, tys)
getTyCons (TypeArrow ty1 ty2) = (qArrowId, [ty1, ty2])
getTyCons _ = internalError "getTyCons"

-- | context reduction
reduceContext :: BT.Context -> BT.Context
reduceContext = undefined

-- |checks whether the given context is valid. If the context returned is
-- empty, the context is valid. Else the returned context contains the 
-- elements of the context that are not valid
-- TODO: consider superclass relations?
isValidCx :: ClassEnv -> BT.Context -> BT.Context
isValidCx cEnv cx = concatMap isValid' cx
  where
  isValid' :: (QualIdent, Type) -> BT.Context
  isValid' (_cls, TypeVariable _) = []
  isValid' (cls, ty) | (isTyCons ty || isArrow ty) = 
    let (xi, tys) = getTyCons ty
        inst = getInstance cEnv cls xi
        tyVars = typeVars (fromJust inst)
        iCx = context (fromJust inst)
        s = zip tyVars tys in
    if isNothing inst then [(cls, ty)]
    else isValidCx cEnv (substContext s iCx)
  isValid' (_cls, _) = []

-- | returns the instance for a given class and type
getInstance :: ClassEnv -> QualIdent -> QualIdent -> Maybe Instance
getInstance cEnv cls ty = 
  listToMaybe $ filter (\i -> iClass i == cls && iType i == ty) (theInstances cEnv)

-- ----------------------------------------------------------------------------
-- Pritty printer functions
-- ----------------------------------------------------------------------------
ppClasses :: ClassEnv -> Doc
ppClasses (ClassEnv classes ifs mmap) = 
  vcat (map ppClass classes) $$ vcat (map ppInst ifs)
  $$ text (show mmap)
  
  
ppClass :: Class -> Doc
ppClass (Class {superClasses = sc, theClass = tc, typeVar = tv, 
                kind = k, methods = ms, defaults = ds, typeSchemes = tscs})
  = text "class<" <> text (show k) <> text ">" 
  <+> parens (hsep $ punctuate (text ",") (map (text . show) sc))
  <> text " => " <> text (show tc)
  <+> text (show tv) <+> text "where"
  $$ vcat (map (\(id0, cx, ty) -> 
                 nest 2 (ppIdent id0 <+> text "::" <+> ppContext cx <+> ppTypeExpr 0 ty))
               ms)
  $$ vcat (map (\(id0, tsc) -> nest 2 (ppIdent id0 <+> text "::" <+> text (show tsc))) tscs) 
  $$ nest 2 (vcat $ map ppDecl ds)

ppInst :: Instance -> Doc
ppInst (Instance {context = cx, iClass = ic, iType = it, typeVars = tvs, rules = rs})
  = text "instance" 
  <+> parens (hsep $ punctuate (text ",") (map (\(qid, tid) -> text (show qid) <+> text (show tid)) cx))
  <> text " => " <> text (show ic) <+> text "(" <> text (show it)
  <+> hsep (map (text. show) tvs) <> text ")" <+> text "where"
  $$ nest 2 (vcat $ map ppDecl rs)
  