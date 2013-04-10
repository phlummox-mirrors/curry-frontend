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
  ( ClassEnv (..), Class (..), Interface (..), initClassEnv, lookupClass, 
    ppClasses
  ) where

import Base.Types hiding (typeVar, typeVars)
import Curry.Base.Ident
import Text.PrettyPrint

data ClassEnv = ClassEnv [Class] [Interface]
  deriving Show

data Class = Class
  { superClasses :: [QualIdent]
  , theClass :: Ident
  , typeVar :: Int -- TODO needed?
  , kind :: Int
  , methods :: [TypeScheme]
  }
  deriving Show

data Interface = Interface
  { context :: [(QualIdent,Ident)]
  , iClass :: QualIdent
  , iType :: QualIdent
  , typeVars :: [Int]
  -- , funcDefinitions :: [???]
  }
  deriving Show
  
initClassEnv :: ClassEnv 
initClassEnv = ClassEnv [] []

lookupClass :: ClassEnv -> Ident -> Maybe Class
lookupClass (ClassEnv cls _) c = lookupClass' cls
  where lookupClass' [] = Nothing
        lookupClass' (c'@Class {theClass=tc}:cs) 
          | tc == c = Just c'
          | otherwise = lookupClass' cs

ppClasses :: ClassEnv -> Doc
ppClasses (ClassEnv classes ifs) = 
  vcat (map ppClass classes) $$ vcat (map ppIf ifs)
  
  
ppClass :: Class -> Doc
ppClass (Class {superClasses = sc, theClass = tc, typeVar = tv, 
                kind = k, methods = ms})
  = text "class<" <> text (show k) <> text ", " <> text (show tv)
  <> text ">" <+> hsep (map (text . show) sc) <> text " => " <> text (show tc)
  <+> hsep (map (text . show) ms) 

ppIf :: Interface -> Doc
ppIf (Interface {context = cx, iClass = ic, iType = it, typeVars = tvs})
  = text "interface" 
  <+> hsep (map (\(qid, tid) -> text (show qid) <+> text (show tid)) cx)
  <> text " => " <> text (show ic) <+> text "(" <> text (show it)
  <+> hsep (map (text. show) tvs) <> text ")"
  