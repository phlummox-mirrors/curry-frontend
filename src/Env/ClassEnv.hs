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
  , lookupDefiningClass, lookupMethodTypeScheme
  , ppClasses
  ) where

-- import Base.Types hiding ()
import Curry.Base.Ident
import Text.PrettyPrint
import Curry.Syntax.Type
import qualified Data.Map as Map
import Curry.Syntax.Pretty
import Control.Monad (liftM)
import Base.Types hiding (Context, typeVar, typeVars)

-- |The class environment consists of the classes and instances in scope
-- plus a map from class methods to their defining classes
data ClassEnv = ClassEnv [Class] [Instance] (Map.Map QualIdent QualIdent) 
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
  , iType :: TypeConstructor
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

lookupMethodTypeScheme :: ClassEnv -> QualIdent -> Maybe TypeScheme
lookupMethodTypeScheme cEnv qid = do
  theClass_ <- lookupDefiningClass cEnv qid
  classMethods <- liftM typeSchemes (lookupClass cEnv theClass_) 
  lookup (unqualify qid) classMethods  

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
  