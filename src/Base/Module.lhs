\paragraph{Interfaces}
The compiler maintains a global environment holding all (directly or
indirectly) imported interfaces.

The function \texttt{bindFlatInterface} transforms FlatInterface
information (type \texttt{FlatCurry.Prog} to MCC interface declarations
(type \texttt{CurrySyntax.IDecl}. This is necessary to process
FlatInterfaces instead of ".icurry" files when using MCC as frontend
for PAKCS.
\begin{verbatim}

> module Base.Module (ModuleEnv, lookupModule) where

> import qualified Data.Map as Map

> import Curry.Base.Ident
> import qualified Curry.Syntax as CS

> type ModuleEnv = Map.Map ModuleIdent [CS.IDecl]

> lookupModule :: ModuleIdent -> ModuleEnv -> Maybe [CS.IDecl]
> lookupModule = Map.lookup

\end{verbatim}
