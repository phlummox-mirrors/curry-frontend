{- |
    Module      :  $Header$
    Description :  Top-Level Environments
    Copyright   :   1999 - 2003 Wolfgang Lux
                    2005        Martin Engelke
                    2011 - 2012 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The module \texttt{TopEnv} implements environments for qualified and
    possibly ambiguous identifiers. An identifier is ambiguous if two
    different entities are imported under the same name or if a local
    definition uses the same name as an imported entity. Following an idea
    presented in \cite{DiatchkiJonesHallgren02:ModuleSystem}, an
    identifier is associated with a list of entities in order to handle
    ambiguous names properly.

    In general, two entities are considered equal if the names of their
    original definitions match. However, in the case of algebraic data
    types it is possible to hide some or all of their data constructors on
    import and export, respectively. In this case we have to merge both
    imports such that all data constructors which are visible through any
    import path are visible in the current module. The class
    \texttt{Entity} is used to handle this merge.

    The code in this module ensures that the list of entities returned by
    the functions \texttt{lookupTopEnv} and \texttt{qualLookupTopEnv}
    contains exactly one element for each imported entity regardless of
    how many times and from which module(s) it was imported. Thus, the
    result of these function is a list with exactly one element if and
    only if the identifier is unambiguous. The module names associated
    with an imported entity identify the modules from which the entity was
    imported.
-}

module Base.TopEnv
  ( -- * Data types
    TopEnv (..), Entity (..)
    -- * creation and insertion
  , emptyTopEnv, predefTopEnv, importTopEnv, qualImportTopEnv
  , bindTopEnv, qualBindTopEnv, rebindTopEnv
  , qualRebindTopEnv, unbindTopEnv, lookupTopEnv, qualLookupTopEnv
  , allImports, moduleImports, localBindings, allLocalBindings 
  , allBindings, allBoundElems
  , tryBindTopEnv, tryQualBindTopEnv, tryRebindTopEnv, tryQualRebindTopEnv
  , filterEnv
  ) where

import           Control.Arrow        (second)
import qualified Data.Map      as Map
  (Map, empty, insert, findWithDefault, lookup, toList, map)

import Control.Monad

import Curry.Base.Ident
import Base.Messages (internalError)

class Entity a where
 origName :: a -> QualIdent
 merge    :: a -> a -> Maybe a
 merge x y
   | origName x == origName y = Just x
   | otherwise                = Nothing

data Source = Local | Import [ModuleIdent] deriving (Eq, Show)

-- |Top level environment
newtype TopEnv a = TopEnv { topEnvMap :: Map.Map QualIdent [(Source, a)] }
  deriving Show

instance Functor TopEnv where
  fmap f (TopEnv env) = TopEnv (fmap (map (second f)) env)

-- local helper
entities :: QualIdent -> Map.Map QualIdent [(Source, a)] -> [(Source, a)]
entities = Map.findWithDefault []

-- |Empty 'TopEnv'
emptyTopEnv :: TopEnv a
emptyTopEnv = TopEnv Map.empty

-- |Insert an 'Entity' into a 'TopEnv' as a predefined 'Entity'
predefTopEnv :: Entity a => QualIdent -> a -> TopEnv a -> TopEnv a
predefTopEnv k v (TopEnv env) = case Map.lookup k env of
  Just  _ -> internalError "TopEnv.predefTopEnv"
  Nothing -> TopEnv $ Map.insert k [(Import [], v)] env

-- |Insert an 'Entity' as unqualified into a 'TopEnv'
importTopEnv :: Entity a => ModuleIdent -> Ident -> a -> TopEnv a
             -> TopEnv a
importTopEnv m x y env = addImport m (qualify x) y env

-- |Insert an 'Entity' as qualified into a 'TopEnv'
qualImportTopEnv :: Entity a => ModuleIdent -> Ident -> a -> TopEnv a
                 -> TopEnv a
qualImportTopEnv m x y env = addImport m (qualifyWith m x) y env

-- local helper
addImport :: Entity a => ModuleIdent -> QualIdent -> a -> TopEnv a
          -> TopEnv a
addImport m k v (TopEnv env) = TopEnv $
  Map.insert k (mergeImport v (entities k env)) env
  where
  mergeImport :: Entity a => a -> [(Source, a)] -> [(Source, a)]
  mergeImport y []                         = [(Import [m], y)]
  mergeImport y (loc@(Local    ,  _) : xs) = loc : mergeImport y xs
  mergeImport y (imp@(Import ms, y') : xs) = case merge y y' of
    Just y'' -> (Import (m : ms), y'') : xs
    Nothing  -> imp : mergeImport y xs

-- various binds

tryBindTopEnv :: String -> Ident -> a -> TopEnv a -> (Maybe (TopEnv a))
tryBindTopEnv fun x y env = tryQualBindTopEnv fun (qualify x) y env

tryQualBindTopEnv :: String -> QualIdent -> a -> TopEnv a -> (Maybe (TopEnv a))
tryQualBindTopEnv _fun x y (TopEnv env) = do
  local <- bindLocal y (entities x env)
  return $ TopEnv $ Map.insert x local env
  where
  bindLocal y' ys
    | null [ y'' | (Local, y'') <- ys ] = Just $ (Local, y') : ys
    | otherwise = Nothing

bindTopEnv :: String -> Ident -> a -> TopEnv a -> (TopEnv a)
bindTopEnv fun x y env = 
  dontTry "bindTopEnv" (qualify x) fun $ tryBindTopEnv fun x y env

qualBindTopEnv :: String -> QualIdent -> a -> TopEnv a -> (TopEnv a)
qualBindTopEnv fun x y env = 
  dontTry "qualBindTopEnv" x fun $ tryQualBindTopEnv fun x y env

dontTry :: String -> QualIdent -> String -> Maybe a -> a 
dontTry name x fun = 
  maybe (internalError $ "\"" ++ show name ++ " " ++ show x
    ++ "\" failed in function \"" ++ fun ++ "\"") id 

-- various rebinds

tryRebindTopEnv :: Ident -> a -> TopEnv a -> Maybe (TopEnv a)
tryRebindTopEnv = tryQualRebindTopEnv . qualify

tryQualRebindTopEnv :: QualIdent -> a -> TopEnv a -> Maybe (TopEnv a)
tryQualRebindTopEnv x y (TopEnv env) = do
  local <- rebindLocal (entities x env)
  return $ TopEnv $ Map.insert x local env
  where
  rebindLocal []                = Nothing -- internalError "TopEnv.qualRebindTopEnv"
  rebindLocal ((Local, _) : ys) = Just $ (Local, y) : ys
  rebindLocal (imported   : ys) = liftM (imported   :) $ rebindLocal ys

qualRebindTopEnv :: QualIdent -> a -> TopEnv a -> TopEnv a
qualRebindTopEnv x y env = dontTry' "qualRebindTopEnv"  $ tryQualRebindTopEnv x y env 

rebindTopEnv :: Ident -> a -> TopEnv a -> TopEnv a
rebindTopEnv x y env = dontTry' "rebindTopEnv" $ tryRebindTopEnv x y env

dontTry' :: String -> Maybe a -> a
dontTry' fun = maybe (internalError fun) id




unbindTopEnv :: Ident -> TopEnv a -> TopEnv a
unbindTopEnv x (TopEnv env) =
  TopEnv $ Map.insert x' (unbindLocal (entities x' env)) env
  where x' = qualify x
        unbindLocal [] = internalError "TopEnv.unbindTopEnv"
        unbindLocal ((Local, _) : ys) = ys
        unbindLocal (imported   : ys) = imported : unbindLocal ys

lookupTopEnv :: Ident -> TopEnv a -> [a]
lookupTopEnv = qualLookupTopEnv . qualify

qualLookupTopEnv :: QualIdent -> TopEnv a -> [a]
qualLookupTopEnv x (TopEnv env) = map snd (entities x env)

allImports :: TopEnv a -> [(QualIdent, a)]
allImports (TopEnv env) =
  [ (x, y) | (x, ys) <- Map.toList env, (Import _, y) <- ys ]

unqualBindings :: TopEnv a -> [(Ident, (Source, a))]
unqualBindings (TopEnv env) =
  [ (x', y) | (x, ys) <- filter (not . isQualified . fst) (Map.toList env)
            , let x' = unqualify x, y <- ys]

moduleImports :: ModuleIdent -> TopEnv a -> [(Ident, a)]
moduleImports m env =
  [(x, y) | (x, (Import ms, y)) <- unqualBindings env, m `elem` ms]

localBindings :: TopEnv a -> [(Ident, a)]
localBindings env = [ (x, y) | (x, (Local, y)) <- unqualBindings env ]

allLocalBindings :: TopEnv a -> [(QualIdent, a)]
allLocalBindings (TopEnv env) = [ (x, y) | (x, ys)    <- Map.toList env
                                         , (Local, y) <- ys ]

allBindings :: TopEnv a -> [(QualIdent, a)]
allBindings (TopEnv env) = [ (x, y) | (x, ys) <- Map.toList env
                                    , (_, y)  <- ys ]

allBoundElems :: TopEnv a -> [a]
allBoundElems (TopEnv env) = [ y | (_, ys) <- Map.toList env
                                 , (_, y) <- ys ]

filterEnv :: (a -> Bool) -> TopEnv a -> TopEnv a
filterEnv p (TopEnv env) = TopEnv $ Map.map filter' env
  where
  -- filter' :: [(Source, a)] -> [(Source, a)]
  filter' = filter p' 
  -- p' :: (Source, a) -> Bool
  p' (_src, x) = p x
