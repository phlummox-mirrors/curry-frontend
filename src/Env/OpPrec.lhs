\paragraph{Operator precedences}
In order to parse infix expressions correctly, the compiler must know
the precedence and fixity of each operator. Operator precedences are
associated with entities and will be checked after renaming was
applied. Nevertheless, we need to save precedences for ambiguous names
in order to handle them correctly while computing the exported
interface of a module.

If no fixity is assigned to an operator, it will be given the default
precedence 9 and assumed to be a left-associative operator.

\em{Note:} this modified version uses Haskell type \texttt{Integer}
for representing the precedence. This change had to be done due to the
introduction of unlimited integer constants in the parser / lexer.
\begin{verbatim}

> module Env.OpPrec
>   ( PEnv, PrecInfo (..), OpPrec (..), defaultP, bindP, lookupP, qualLookupP
>   , initPEnv ) where

> import Curry.Base.Ident
> import qualified Curry.Syntax as CS

> import Env.TopEnv

> data OpPrec = OpPrec CS.Infix Integer deriving Eq

> instance Show OpPrec where
>   showsPrec _ (OpPrec fix p) = showString (assoc fix) . shows p
>     where assoc CS.InfixL = "left "
>           assoc CS.InfixR = "right "
>           assoc CS.Infix  = "non-assoc "

> defaultP :: OpPrec
> defaultP = OpPrec CS.InfixL 9

\end{verbatim}
The lookup functions for the environment which maintains the operator
precedences are simpler than for the type and value environments
because they do not need to handle tuple constructors.
\begin{verbatim}

> data PrecInfo = PrecInfo QualIdent OpPrec deriving (Eq, Show)

> instance Entity PrecInfo where
>   origName (PrecInfo op _) = op

> type PEnv = TopEnv PrecInfo

> bindP :: ModuleIdent -> Ident -> OpPrec -> PEnv -> PEnv
> bindP m op p
>   | uniqueId op == 0
>     = bindTopEnv "Base.bindP" op info . qualBindTopEnv "Base.bindP" op' info
>   | otherwise = bindTopEnv "Base.bindP" op info
>   where op' = qualifyWith m op
>         info = PrecInfo op' p

> lookupP :: Ident -> PEnv -> [PrecInfo]
> lookupP = lookupTopEnv

> qualLookupP :: QualIdent -> PEnv -> [PrecInfo]
> qualLookupP = qualLookupTopEnv

> initPEnv :: PEnv
> initPEnv =
>   predefTopEnv qConsId (PrecInfo qConsId (OpPrec CS.InfixR 5)) emptyTopEnv

\end{verbatim}
