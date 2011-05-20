\paragraph{Module aliases}
\begin{verbatim}

> module Base.Import
>   ( ImportEnv, bindAlias, lookupAlias, sureLookupAlias, initIEnv
>   , fromDeclList
>   ) where

> import qualified Data.Map as Map (Map, empty, insert, lookup)
> import Data.Maybe (fromMaybe)

> import Curry.Base.Ident (ModuleIdent)
> import qualified Curry.Syntax as CS (Decl (..))

> type ImportEnv = Map.Map ModuleIdent ModuleIdent

> bindAlias :: CS.Decl -> ImportEnv -> ImportEnv
> bindAlias (CS.ImportDecl _ mid _ alias _)
>   = Map.insert mid $ fromMaybe mid alias
> bindAlias _ = error "Base.bindAlias: no import declaration"

> fromDeclList :: [CS.Decl] -> ImportEnv
> fromDeclList = foldr bindAlias initIEnv

> lookupAlias :: ModuleIdent -> ImportEnv -> Maybe ModuleIdent
> lookupAlias = Map.lookup

> sureLookupAlias :: ModuleIdent -> ImportEnv -> ModuleIdent
> sureLookupAlias m = fromMaybe m . lookupAlias m

> initIEnv :: ImportEnv
> initIEnv = Map.empty

\end{verbatim}
