% -*- LaTeX -*-
% $Id: Error.lhs,v 1.1 2003/05/07 22:38:42 wlux Exp $
%
% Copyright (c) 2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Error.lhs}
\section{Errors}\label{sec:error}
The \texttt{Error} type is used for describing the result of a
computation that can fail. In contrast to the standard \texttt{Maybe}
type, its \texttt{Error} case provides for an error message that
describes the failure.
\begin{verbatim}

> module Curry.Syntax.ParseResult where
> import Control.Monad

> data Error a = Ok a | Error String deriving (Eq,Ord,Show)

> instance Functor Error where
>   fmap f (Ok x) = Ok (f x)
>   fmap f (Error e) = Error e

> instance Monad Error where
>   return x = Ok x
>   fail s = Error s
>   Ok x >>= f = f x
>   Error e >>= _ = Error e

> ok :: Error a -> a
> ok (Ok x) = x
> ok (Error e) = error e


\end{verbatim}
