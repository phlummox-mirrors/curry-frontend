module Base.OldScopeEnv
  ( ScopeEnv, newScopeEnv, beginScope, insertIdent, genIdentList
  ) where

import qualified Data.Map as Map

import Curry.Base.Ident

-- The IdEnv is an environment which stores the level in which an identifier
-- was defined, starting with 0 for the top-level.
type IdEnv = Map.Map IdRep Integer
data IdRep = Name String | Index Integer deriving (Eq, Ord)

insertId :: Integer -> Ident -> IdEnv -> IdEnv
insertId level ident = Map.insert (Name  (idName   ident)) level
                     . Map.insert (Index (idUnique ident)) level

nameExists :: String -> IdEnv -> Bool
nameExists name = Map.member (Name name)

indexExists :: Integer -> IdEnv -> Bool
indexExists index = Map.member (Index index)

genId :: String -> IdEnv -> Maybe Ident
genId n env
   | nameExists n env = Nothing
   | otherwise        = Just (p_genId (mkIdent n) 0)
 where
   p_genId ident index
      | indexExists index env = p_genId ident (index + 1)
      | otherwise             = renameIdent ident index

{- Type for representing an environment containing identifiers in several
   scope levels -}
type ScopeLevel = Integer
type ScopeEnv   = (IdEnv, [IdEnv], ScopeLevel)
-- (top-level IdEnv, stack of lower level IdEnv, current level)
-- Invariant: The current level is the number of stack elements

-- Generates a new instance of a scope table
newScopeEnv :: ScopeEnv
newScopeEnv = (Map.empty, [], 0)

-- Insert an identifier into the current level of the scope environment
insertIdent :: Ident -> ScopeEnv -> ScopeEnv
insertIdent ident (topleveltab, leveltabs, level) = case leveltabs of
  []       -> ((insertId level ident topleveltab), [], 0)
  (lt:lts) -> (topleveltab, (insertId level ident lt) : lts, level)

-- Increase the level of the scope.
beginScope :: ScopeEnv -> ScopeEnv
beginScope (topleveltab, leveltabs, level) = case leveltabs of
  []       -> (topleveltab, [Map.empty], 1)
  (lt:lts) -> (topleveltab, (lt:lt:lts), level + 1)

-- Generates a list of new identifiers where each identifier has
-- the prefix 'name' followed by  an index (i.e. "var3" if 'name' was "var").
-- All returned identifiers are unique within the current scope.
genIdentList :: Int -> String -> ScopeEnv -> [Ident]
genIdentList size name scopeenv = p_genIdentList size name scopeenv 0
  where
    p_genIdentList :: Int -> String -> ScopeEnv -> Int -> [Ident]
    p_genIdentList s n env i
      | s == 0    = []
      | otherwise = maybe (p_genIdentList s n env (i + 1))
                          (\ident -> ident:(p_genIdentList (s - 1)
                          n
                          (insertIdent ident env)
                          (i + 1)))
                          (genIdent (n ++ (show i)) env)

-- Generates a new identifier for the specified name. The new identifier is
-- unique within the current scope. If no identifier can be generated for
-- 'name' then 'Nothing' will be returned
genIdent :: String -> ScopeEnv -> Maybe Ident
genIdent name (topleveltab, leveltabs, _) = case leveltabs of
  []     -> genId name topleveltab
  (lt:_) -> genId name lt

-- -- Return the declaration level of an identifier if it exists
-- getIdentLevel :: Ident -> ScopeEnv -> Maybe Integer
-- getIdentLevel ident (topleveltab, leveltabs, _) = case leveltabs of
--   []     -> getIdLevel ident topleveltab
--   (lt:_) -> maybe (getIdLevel ident topleveltab) Just (getIdLevel ident lt)

-- -- Checkswhether the specified identifier is visible in the current scope
-- -- (i.e. check whether the identifier occurs in the scope environment)
-- isVisible :: Ident -> ScopeEnv -> Bool
-- isVisible ident (topleveltab, leveltabs, _) = case leveltabs of
--   []     -> idExists ident topleveltab
--   (lt:_) -> idExists ident lt || idExists ident topleveltab
--
-- -- Check whether the specified identifier is declared in the
-- -- current scope (i.e. checks whether the identifier occurs in the
-- -- current level of the scope environment)
-- isDeclared :: Ident -> ScopeEnv -> Bool
-- isDeclared ident (topleveltab, leveltabs, level) = case leveltabs of
--   []     -> maybe False ((==) 0) (getIdLevel ident topleveltab)
--   (lt:_) -> maybe False ((==) level) (getIdLevel ident lt)

-- -- Decrease the level of the scope. Identifier from higher levels
-- -- will be lost.
-- endScope :: ScopeEnv -> ScopeEnv
-- endScope (topleveltab, leveltabs, level) = case leveltabs of
--   []      -> (topleveltab, [], 0)
--   (_:lts) -> (topleveltab, lts, level - 1)

-- -- Return the level of the current scope. Top level is 0
-- getLevel :: ScopeEnv -> ScopeLevel
-- getLevel (_, _, level) = level

-- idExists :: Ident -> IdEnv -> Bool
-- idExists ident = indexExists (uniqueId ident)

-- getIdLevel :: Ident -> IdEnv -> Maybe Integer
-- getIdLevel ident = Map.lookup (Index (uniqueId ident))
