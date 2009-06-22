
% $Id: PathUtils.lhs,v 1.5 2003/05/04 16:12:35 wlux Exp $
%
% Copyright (c) 1999-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PathUtils.lhs}
\section{Pathnames}
This module implements some utility functions for manipulating path
names and finding files.
\begin{verbatim}

> module PathUtils(basename, rootname,extension, catPath,
>                  lookupFile,
>                  currySubdir,writeModule,readModule,
>                  doesModuleExist,maybeReadModule,getModuleModTime) where

> import System.FilePath
> import System.Directory
> import CurrySubdir

\end{verbatim}

Most of this module is superseded by System.FilePath from package filepath.

Within this module we assume Unix style path semantics, i.e.\ 
components of a path name are separated by forward slash characters
(\texttt{/}) and file extensions are separated with a dot character
(\texttt{.}).

\end{verbatim}

> catPath :: FilePath -> FilePath -> FilePath
> catPath = combine
>
> rootname, extension :: FilePath -> FilePath
> rootname = dropExtension
> extension = takeExtension

\end{verbatim}

The function \texttt{lookupFile} can be used to search for files. It
returns the first name from the argument list for which a regular file
exists in the file system.
\begin{verbatim}

> lookupFile :: [FilePath] -> IO (Maybe FilePath)
> lookupFile fns = lookupFile' (concatMap (\ fn -> [inCurrySubdir fn,fn]) fns)
>   where
>     lookupFile' [] = return Nothing
>     lookupFile' (fn:fns) =
>      do
>       so <- doesFileExist fn
>       if so then return (Just fn) else lookupFile' fns

\end{verbatim}




