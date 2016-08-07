{- |
    Module      :  $Header$
    Description :  Environment of classes
    Copyright   :  (c) 2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains information about all type classes in an
    environment that maps type classes to a list of their direct
    superclasses and all their associated class methods. For both
    the type class identifier and the list of super classes original
    names are used. Thus, the use of a flat environment is sufficient.
-}

module Env.Class
  ( ClassEnv, initClassEnv
  , ClassInfo, bindClassInfo, lookupClassInfo
  , superClasses, allSuperClasses, classMethods
  ) where

import           Data.List       (nub)
import qualified Data.Map as Map (Map, empty, insert, lookup)

import Curry.Base.Ident

import Base.Messages (internalError)

type ClassInfo = ([QualIdent], [Ident])

type ClassEnv = Map.Map QualIdent ClassInfo

initClassEnv :: ClassEnv
initClassEnv = Map.empty

bindClassInfo :: QualIdent -> ClassInfo -> ClassEnv -> ClassEnv
bindClassInfo = Map.insert

lookupClassInfo :: QualIdent -> ClassEnv -> Maybe ClassInfo
lookupClassInfo = Map.lookup

superClasses :: QualIdent -> ClassEnv -> [QualIdent]
superClasses cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (sclss, _) -> sclss
  _ -> internalError $ "Env.Classes.superClasses: " ++ show cls

allSuperClasses :: QualIdent -> ClassEnv -> [QualIdent]
allSuperClasses cls clsEnv = nub $ classes cls
  where
    classes cls' = cls' : concatMap classes (superClasses cls' clsEnv)

classMethods :: QualIdent -> ClassEnv -> [Ident]
classMethods cls clsEnv = case lookupClassInfo cls clsEnv of
  Just (_, ms) -> ms
  _ -> internalError $ "Env.Classes.classMethods: " ++ show cls
