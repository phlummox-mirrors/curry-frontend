% -*- LaTeX -*-
% $Id: Env.lhs,v 1.9 2002/12/20 15:07:56 lux Exp $
%
% Copyright (c) 2002, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Env.lhs}
\section{Environments}
The module \texttt{Env} implements environments. An environment
$\rho = \left\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\right\}$ is a
finite mapping from (finitely many) variables $x_1,\dots,x_n$ to
some kind of expression or term. For any environment we have the
following definitions:
\begin{displaymath}
  \begin{array}{l}
    \rho(x) = \left\{\begin{array}{ll}
        t_i&\mbox{if $x=x_i$}\\
        \bot&\mbox{otherwise}\end{array}\right. \\
    \mathop{{\mathcal D}om}(\rho) = \left\{x_1,\dots,x_n\right\} \\
    \mathop{{\mathcal C}odom}(\rho) = \left\{t_1,\dots,t_n\right\}
  \end{array}
\end{displaymath}

Unfortunately we cannot define \texttt{Env} as a \texttt{newtype}
because of a bug in the nhc compiler.
\begin{verbatim}

> module Env where

> import qualified Data.Map as Map

> newtype Env a b = Env (Map.Map a b) deriving Show

> emptyEnv :: Ord a => Env a b
> emptyEnv = Env Map.empty

> environment :: Ord a => [(a,b)] -> Env a b
> environment l = Env (Map.fromList l)

> envToList :: Ord v => Env v e -> [(v,e)]
> envToList (Env rho) = Map.toList rho

> bindEnv :: Ord v => v -> e -> Env v e -> Env v e
> bindEnv v e (Env rho) = Env (Map.insert v e rho)

> unbindEnv :: Ord v => v -> Env v e -> Env v e
> unbindEnv v (Env rho) = Env (Map.delete v rho)

> lookupEnv :: Ord v => v -> Env v e -> Maybe e
> lookupEnv v (Env rho) = Map.lookup v rho

> envSize :: Ord v => Env v e -> Int
> envSize (Env rho) = Map.size rho

> instance Ord a => Functor (Env a) where
>   fmap f (Env rho) = Env (fmap f rho)

\end{verbatim}
