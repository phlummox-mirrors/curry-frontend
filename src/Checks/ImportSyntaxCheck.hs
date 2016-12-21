{- |
    Module      :  $Header$
    Description :  Checking import specifications
    Copyright   :  (c) 2016       Jan Tikovsky
    License     :  BSD-3-clause

    Maintainer  :  jrt@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module provides the function 'importCheck' to check and expand
    the import specifications of all import declarations.
-}
module Checks.ImportSyntaxCheck(importCheck) where

import           Control.Monad              (liftM, unless)
import qualified Control.Monad.State as S   (State, gets, modify, runState)
import Data.List                            (nub, union)
import qualified Data.Map            as Map
import           Data.Maybe                 (fromMaybe)

import Curry.Base.Ident
import Curry.Base.Pretty
import Curry.Syntax

import Base.Messages
import Base.TopEnv



importCheck :: Interface -> Maybe ImportSpec -> (Maybe ImportSpec, [Message])
importCheck (Interface m _ ds) is = runExpand (expandSpecs is) m mTCEnv mTyEnv
  where
  mTCEnv = intfEnv types  ds
  mTyEnv = intfEnv values ds

data ITypeInfo = Data  QualIdent [Ident]
               | Alias QualIdent
 deriving Show

instance Entity ITypeInfo where
  origName (Data tc _) = tc
  origName (Alias  tc) = tc

  merge (Data tc1 cs1) (Data tc2 cs2)
    | tc1 == tc2 && (null cs1 || null cs2 || cs1 == cs2) =
        Just $ Data tc1 (if null cs1 then cs2 else cs1)
  merge l@(Alias tc1) (Alias tc2)
    | tc1 == tc2 = Just l
  merge _ _ = Nothing

data IValueInfo = Constr QualIdent
                | Var    QualIdent [QualIdent]
 deriving Show

instance Entity IValueInfo where
  origName (Constr c) = c
  origName (Var  x _) = x

  merge (Constr c1) (Constr c2)
    | c1 == c2 = Just (Constr c1)
  merge (Var x1 cs1) (Var x2 cs2)
    | x1 == x2 = Just (Var x1 (cs1 `union` cs2))
  merge _ _ = Nothing


intfEnv :: Entity a => (IDecl -> [a]) -> [IDecl] -> IdentMap a
intfEnv idents ds = foldr bindId Map.empty (concatMap idents ds)
  where bindId x = Map.insert (unqualify (origName x)) x

types :: IDecl -> [ITypeInfo]
types (IDataDecl    _ tc _ cs hs) = [Data tc (filter (`notElem` hs) xs)]
  where xs = map constrId cs ++ nub (concatMap recordLabels cs)
types (INewtypeDecl _ tc _ nc hs) = [Data tc (filter (`notElem` hs) xs)]
  where xs = nconstrId nc : nrecordLabels nc
types (ITypeDecl        _ tc _ _) = [Alias tc]
types _                           = []

values :: IDecl -> [IValueInfo]
values (IDataDecl    _ tc _ cs hs) =
  cidents tc (map constrId cs) hs ++
  lidents tc [(l, lconstrs cs l) | l <- nub (concatMap recordLabels cs)] hs
  where lconstrs cons l = [constrId c | c <- cons, l `elem` recordLabels c]
values (INewtypeDecl _ tc _ nc hs) =
  cidents tc [nconstrId nc] hs ++
  lidents tc [(l, [c]) | NewRecordDecl _ _ c (l, _) <- [nc]] hs
values (IFunctionDecl     _ f _ _) = [Var f []]
values _                           = []

cidents :: QualIdent -> [Ident] -> [Ident] -> [IValueInfo]
cidents tc cs hs = [Constr (qualifyLike tc c) | c <- cs, c `notElem` hs]

lidents :: QualIdent -> [(Ident, [Ident])] -> [Ident] -> [IValueInfo]
lidents tc ls hs = [ Var (qualifyLike tc l) (map (qualifyLike tc) cs)
                   | (l, cs) <- ls, l `notElem` hs
                   ]

-- ---------------------------------------------------------------------------
-- Expansion of the import specification
-- ---------------------------------------------------------------------------

-- After the environments have been initialized, the optional import
-- specifications can be checked. There are two kinds of import
-- specifications, a ``normal'' one, which names the entities that shall
-- be imported, and a hiding specification, which lists those entities
-- that shall not be imported.
--
-- There is a subtle difference between both kinds of
-- specifications: While it is not allowed to list a data constructor
-- outside of its type in a ``normal'' specification, it is allowed to
-- hide a data constructor explicitly. E.g., if module \texttt{A} exports
-- the data type \texttt{T} with constructor \texttt{C}, the data
-- constructor can be imported with one of the two specifications
--
-- import A (T(C))
-- import A (T(..))
--
-- but can be hidden in three different ways:
--
-- import A hiding (C)
-- import A hiding (T (C))
-- import A hiding (T (..))
--
-- The functions \texttt{expandImport} and \texttt{expandHiding} check
-- that all entities in an import specification are actually exported
-- from the module. In addition, all imports of type constructors are
-- changed into a \texttt{T()} specification and explicit imports for the
-- data constructors are added.

type IdentMap    = Map.Map Ident

type ExpTCEnv    = IdentMap ITypeInfo
type ExpValueEnv = IdentMap IValueInfo

data ExpandState = ExpandState
  { expModIdent :: ModuleIdent
  , expTCEnv    :: ExpTCEnv
  , expValueEnv :: ExpValueEnv
  , errors      :: [Message]
  }

type ExpandM a = S.State ExpandState a

getModuleIdent :: ExpandM ModuleIdent
getModuleIdent = S.gets expModIdent

getTyConsEnv :: ExpandM ExpTCEnv
getTyConsEnv = S.gets expTCEnv

getValueEnv :: ExpandM ExpValueEnv
getValueEnv = S.gets expValueEnv

report :: Message -> ExpandM ()
report msg = S.modify $ \ s -> s { errors = msg : errors s }

runExpand :: ExpandM a -> ModuleIdent -> ExpTCEnv -> ExpValueEnv -> (a, [Message])
runExpand expand m tcEnv tyEnv =
  let (r, s) = S.runState expand (ExpandState m tcEnv tyEnv [])
  in (r, reverse $ errors s)

expandSpecs :: Maybe ImportSpec -> ExpandM (Maybe ImportSpec)
expandSpecs Nothing                 = return Nothing
expandSpecs (Just (Importing p is)) = (Just . Importing p . concat) `liftM` mapM expandImport is
expandSpecs (Just (Hiding    p is)) = (Just . Hiding    p . concat) `liftM` mapM expandHiding is

expandImport :: Import -> ExpandM [Import]
expandImport (Import             x) =               expandThing    x
expandImport (ImportTypeWith tc cs) = (:[]) `liftM` expandTypeWith tc cs
expandImport (ImportTypeAll     tc) = (:[]) `liftM` expandTypeAll  tc

expandHiding :: Import -> ExpandM [Import]
expandHiding (Import             x) = expandHide x
expandHiding (ImportTypeWith tc cs) = (:[]) `liftM` expandTypeWith tc cs
expandHiding (ImportTypeAll     tc) = (:[]) `liftM` expandTypeAll  tc

-- try to expand as type constructor
expandThing :: Ident -> ExpandM [Import]
expandThing tc = do
  tcEnv <- getTyConsEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandThing' tc $ Just [ImportTypeWith tc []]
    Nothing -> expandThing' tc Nothing

-- try to expand as function / data constructor
expandThing' :: Ident -> Maybe [Import] -> ExpandM [Import]
expandThing' f tcImport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  expand m f (Map.lookup f tyEnv) tcImport
  where
  expand :: ModuleIdent -> Ident
         -> Maybe IValueInfo -> Maybe [Import] -> ExpandM [Import]
  expand m e Nothing  Nothing   = report (errUndefinedEntity m e) >> return []
  expand _ _ Nothing  (Just tc) = return tc
  expand m e (Just v) maybeTc
    | isConstr v = case maybeTc of
        Nothing -> report (errImportDataConstr m e) >> return []
        Just tc -> return tc
    | otherwise  = return [Import e]

  isConstr (Constr _) = True
  isConstr (Var  _ _) = False

-- try to hide as type constructor
expandHide :: Ident -> ExpandM [Import]
expandHide tc = do
  tcEnv <- getTyConsEnv
  case Map.lookup tc tcEnv of
    Just _  -> expandHide' tc $ Just [ImportTypeWith tc []]
    Nothing -> expandHide' tc Nothing

-- try to hide as function / data constructor
expandHide' :: Ident -> Maybe [Import] -> ExpandM [Import]
expandHide' f tcImport = do
  m     <- getModuleIdent
  tyEnv <- getValueEnv
  case Map.lookup f tyEnv of
    Just _  -> return $ Import f : fromMaybe [] tcImport
    Nothing -> case tcImport of
      Nothing -> report (errUndefinedEntity m f) >> return []
      Just tc -> return tc

expandTypeWith ::  Ident -> [Ident] -> ExpandM Import
expandTypeWith tc cs = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  ImportTypeWith tc `liftM` case Map.lookup tc tcEnv of
    Just (Data _ xs) -> mapM (checkElement xs) cs
    Just (Alias   _) -> report (errNonDataType       tc) >> return []
    Nothing          -> report (errUndefinedEntity m tc) >> return []
  where
  -- check if given identifier is constructor or label of type tc
  checkElement cs' c = do
    unless (c `elem` cs') $ report $ errUndefinedElement tc c
    return c

expandTypeAll :: Ident -> ExpandM Import
expandTypeAll tc = do
  m     <- getModuleIdent
  tcEnv <- getTyConsEnv
  ImportTypeWith tc `liftM` case Map.lookup tc tcEnv of
    Just (Data _ xs) -> return xs
    Just (Alias   _) -> report (errNonDataType       tc) >> return []
    Nothing          -> report (errUndefinedEntity m tc) >> return []

-- error messages

errUndefinedElement :: Ident -> Ident -> Message
errUndefinedElement tc c = posMessage c $ hsep $ map text
  [ idName c, "is not a constructor or label of type ", idName tc ]

errUndefinedEntity :: ModuleIdent -> Ident -> Message
errUndefinedEntity m x = posMessage x $ hsep $ map text
  [ "Module", moduleName m, "does not export", idName x ]

errNonDataType :: Ident -> Message
errNonDataType tc = posMessage tc $ hsep $ map text
  [ idName tc, "is not a data type" ]

errImportDataConstr :: ModuleIdent -> Ident -> Message
errImportDataConstr _ c = posMessage c $ hsep $ map text
  [ "Explicit import for data constructor", idName c ]
