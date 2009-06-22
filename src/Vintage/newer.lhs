% -*- LaTeX -*-
% $Id: newer.lhs,v 1.1 2002/11/10 05:30:20 lux Exp $
%
% Copyright (c) 2002, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{newer.lhs}
\section{Compute whether a file is out-of-date}
Unfortunately, not all versions of the Unix \verb|test| program
support the switches \verb|-nt| and \verb|-ot| to compare the
modification dates of their arguments. Even worse, on some systems
(e.g., Solaris 2.7) the \verb|test| program supports these switches
but the default Bourne shell has a builtin \verb|test| that does not
handle these switches.

In order to avoid complex dependencies on the operating system we
use our own program in order to check whether a file is out-of-date
-- i.e. newer than -- with respect to some other files it depends
on. If checked file does not exist it is considered out-of-date as
well and an error occurs if any of the dependencies does not exist.

The program exits with return code 0 if the file is not out-of-date
and 1 otherwise. In case of an error, the program exits with return
code 2.
\begin{verbatim}

> import IO
> import Directory
> import System
> import Time
> import PathUtils (getModuleModTime)

> main =
>   do
>     prog <- getProgName
>     args <- getArgs
>     b <- newer prog args
>     exitWith (if b then ExitSuccess else ExitFailure 1)

> badUsage prog =
>   do
>     putErrLn ("usage: " ++ prog ++ " FILE DEPENDENCIES...")
>     exitWith (ExitFailure 2)

> newer prog [] = badUsage prog
> newer prog (file:deps) =
>   catch (do t <- getModuleModTime file; allM (isNewer t) deps)
>         (const (return False))

> isNewer t file =
>   catch (do t' <-  getModuleModTime file; return (t > t'))
>         (\ioe -> do print ioe; exitWith (ExitFailure 2))

> allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
> allM f xs = andM (map f xs)

> andM :: Monad m => [m Bool] -> m Bool
> andM = foldr (>>&) (return True)
>   where m1 >>& m2 = m1 >>= \b -> if b then m2 else return False

\end{verbatim}
Unfortunately, the \texttt{hPutStrLn} function is not defined hbc's
\texttt{IO} library.
\begin{verbatim}

> putErr s = hPutStr stderr s
> putErrLn s = putErr (s ++ "\n")

\end{verbatim}