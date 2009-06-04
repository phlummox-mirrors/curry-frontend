
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

> module PathUtils(pathSep,curDirPath, isRelative,isAbsolute,
>                  dirname,basename, rootname,extension, catPath,
>                  listSep, pathList, lookupFile,
>                  currySubdir,writeModule,readModule,
>                  doesModuleExist,maybeReadModule,getModuleModTime) where
> -- import List
> import Directory
> import CurrySubdir

\end{verbatim}
Within this module we assume Unix style path semantics, i.e.\ 
components of a path name are separated by forward slash characters
(\texttt{/}) and file extensions are separated with a dot character
(\texttt{.}).
\begin{verbatim}


\end{verbatim}
Absolute path names start with a slash while relative paths don't.
\begin{verbatim}

> isRelative,isAbsolute :: FilePath -> Bool
> isRelative = not . isAbsolute
> isAbsolute "" = False
> isAbsolute (c:cs) = c == pathSep

\end{verbatim}
Path concatenation on Unix systems is trivial as an empty path also
denotes the current directory. Therefore \texttt{a///b},
\texttt{a/././b}, and \texttt{a/b} all denote the same path.
Nevertheless, we try to avoid inserting redundant slashes here in
order to increase portability.

Note that \texttt{catPath} \emph{dir} \emph{file} ignores \emph{dir}
when \emph{file} is an absolute path.
\begin{verbatim}

> catPath :: FilePath -> FilePath -> FilePath
> catPath dir file
>   | isAbsolute file = file
>   | null dir = file
>   | otherwise = dir ++ if last dir == pathSep then file else pathSep:file

\end{verbatim}
The function \texttt{canonPath} removes redundant path separators from
a file path. In particular, this will remove trailing path separators
from a file path. This behavior is compatible with the standard Unix
tools \texttt{dirname} and \texttt{basename}.

\ToDo{Remove redundant occurrences of \texttt{.} and \texttt{..} in
the path.}

\ToDo{Provide a more general function which performs \texttt{\~}
expansion. Note that such a function will have type \texttt{FilePath
-> IO FilePath}. Also note that the expansion of \texttt{\~}\emph{user}
cannot be implemented portably in Haskell 98.}
\begin{verbatim}


\end{verbatim}
The extension of a filename is the component starting at the last dot
of the filename. Note that only an extension in the basename will be
considered. Also note that the extension will always start with a dot.
\begin{verbatim}

> rootname, extension :: FilePath -> FilePath
> rootname = fst . splitExt 
> extension = snd . splitExt 

> splitExt :: FilePath -> (FilePath,String)
> splitExt path = break ('.'==) (basename path) 

\end{verbatim}
Conventionally the colon is used on Unix system to separate
directories in a list of path specifications. The function
\texttt{pathList} converts a single string containing these separators
into a list of strings.
\begin{verbatim}

> listSep :: Char
> listSep = ':'

> pathList :: String -> [String]
> pathList = separateBy (==listSep)


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




