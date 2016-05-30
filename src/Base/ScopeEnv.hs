{- |ScopeEnv - provides functions and data types for dealing with nested
               scope environments to store data from nested scopes

    This module should be imported using "import qualified" to avoid name
    clashes

    November 2005,
    Martin Engelke (men@informatik.uni-kiel.de)
-}
module Base.ScopeEnv
  ( Level, ScopeEnv
  , new, insert, modify, lookup, level, lookupWithLevel, exists, beginScope
  , endScope, endScopeUp, toLevelList, currentLevel
  ) where

import Prelude hiding (lookup)
import qualified Data.Map as Map

type Level = Int
type LevelMap a b = Map.Map a (b, Level)

-- |Data type for representing information in nested scopes.
data ScopeEnv a b = ScopeEnv Level (LevelMap a b) [LevelMap a b]
  deriving Show

-- |Returns an empty scope environment
new :: ScopeEnv a b
new = ScopeEnv 0 Map.empty []

-- |Inserts a value under a key into the environment of the current scope
insert :: Ord a => a -> b -> ScopeEnv a b -> ScopeEnv a b
insert k v = modifySE insertLev
  where insertLev lev = Map.insert k (v, lev)

-- |Modifies the value of an existing key by applying the function 'fun'
-- in the environment of the current scope
modify :: Ord a => (b -> b) -> a -> ScopeEnv a b -> ScopeEnv a b
modify f k = modifySE modifyLev
  where modifyLev _ = Map.adjust (\ (v, l) -> (f v, l)) k

-- |Looks up the value which is stored under a key from the environment of
-- the current scope
lookup :: Ord a => a -> ScopeEnv a b -> Maybe b
lookup k = fmap fst . lookupWithLevel k

-- Returns the level of the last insertion of a key
level :: Ord a => a -> ScopeEnv a b -> Level
level k = maybe (-1) snd . lookupWithLevel k

-- |Looks up the value and the level which is stored under a key from the
-- environment of the current scope
lookupWithLevel :: Ord a => a -> ScopeEnv a b -> Maybe (b, Level)
lookupWithLevel k = selectSE lookupLev
  where lookupLev _ = Map.lookup k

-- Checks, whether a key exists in the environment of the current scope
exists :: Ord a => a -> ScopeEnv a b -> Bool
exists k = selectSE existsLev
 where existsLev _ = Map.member k

-- Switches to the next scope (i.e. pushes the environment of the current
-- scope onto the top of an scope stack and increments the level counter)
beginScope :: ScopeEnv a b -> ScopeEnv a b
beginScope (ScopeEnv lev top []    ) = ScopeEnv (lev + 1) top [top]
beginScope (ScopeEnv lev top (l:ls)) = ScopeEnv (lev + 1) top (l:l:ls)

-- Switches to the previous scope (i.e. pops the environment from the top
-- of the scope stack and decrements the level counter)
endScope :: ScopeEnv a b -> ScopeEnv a b
endScope (ScopeEnv _   top []    ) = ScopeEnv 0         top []
endScope (ScopeEnv lev top (_:ls)) = ScopeEnv (lev - 1) top ls

-- Behaves like 'endScope' but additionally updates the environment of
-- the previous scope by updating all keys with the corresponding values
-- from the popped environment
endScopeUp :: Ord a => ScopeEnv a b -> ScopeEnv a b
endScopeUp (ScopeEnv _   top []       ) = ScopeEnv 0 top []
endScopeUp (ScopeEnv _   top (l:[])   ) = ScopeEnv 0 (integrate l top) []
endScopeUp (ScopeEnv lev top (l:l':ls)) = ScopeEnv (lev - 1) top
  (integrate l l' : ls)

-- Return all (key, value) pairs from the environment of the current scope
-- which have been inserted in the current level
toLevelList :: ScopeEnv a b -> [(a, b)]
toLevelList = selectSE toList
 where toList lev local
        = [ (k, v) | (k, (v, lev')) <- Map.toList local, lev' == lev ]

-- Return the current level
currentLevel :: ScopeEnv a b -> Level
currentLevel = selectSE const

-- ---------------------------------------------------------------------------
-- Privates
-- ---------------------------------------------------------------------------

modifySE :: (Level -> LevelMap a b -> LevelMap a b)
         -> ScopeEnv a b -> ScopeEnv a b
modifySE f (ScopeEnv _   top []    ) = ScopeEnv 0   (f 0 top) []
modifySE f (ScopeEnv lev top (l:ls)) = ScopeEnv lev top       (f lev l : ls)

selectSE :: (Level -> LevelMap a b -> c) -> ScopeEnv a b -> c
selectSE f (ScopeEnv _   top []   ) = f 0   top
selectSE f (ScopeEnv lev _   (l:_)) = f lev l

integrate :: Ord a => LevelMap a b -> LevelMap a b -> LevelMap a b
integrate local = Map.mapWithKey update
  where update k old@(_, l) = case Map.lookup k local of
          Nothing         -> old
          Just (v', l')
            | l == l'   -> (v', l)
            | otherwise -> old
