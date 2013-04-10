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

typeClassesCheck :: [Decl] -> ClassEnv -> ([Decl], ClassEnv, [Message])
typeClassesCheck decls cenv = 
  let 
    (classDecls, rest) = extractClassDecls decls
    -- TODO: do checks
    classes = map classDeclToClass classDecls
  in (rest, ClassEnv classes [], [])

extractClassDecls :: [Decl] -> ([Decl], [Decl])
extractClassDecls = partition isClass
  where isClass (ClassDecl _ _ _ _ _) = True
        isClass _ = False
        
classDeclToClass :: Decl -> Class
classDeclToClass (ClassDecl _ (SContext scon) cls tyvar types) 
  = Class { 
    superClasses = map fst scon, 
    theClass = cls, 
    typeVar = 0, -- TODO
    kind = -1, -- TODO
    methods = [] -- TODO
  }