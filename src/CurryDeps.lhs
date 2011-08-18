% $Id: CurryDeps.lhs,v 1.14 2004/02/09 17:10:05 wlux Exp $
%
% Copyright (c) 2002-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke    (men@informatik.uni-kiel.de)
% Extended by Sebastian Fischer (sebf@informatik.uni-kiel.de)
% Modified by Bjoern Peemoeller (bjp@informatik.uni-kiel.de)
%
\nwfilename{CurryDeps.lhs}
\section{Building Programs}
This module implements the functions to compute the dependency
information between Curry modules. This is used to create Makefile
dependencies and to update programs composed of multiple modules.
\begin{verbatim}

> module CurryDeps
>   ( Source (..), flatDeps, deps, flattenDeps, sourceDeps, moduleDeps ) where

> import Control.Monad (foldM, liftM, unless)
> import Data.List (isSuffixOf, nub)
> import qualified Data.Map as Map (Map, empty, insert, lookup, toList)

> import Curry.Base.Ident
> import Curry.Base.MessageMonad
> import Curry.Files.Filenames
> import Curry.Files.PathUtils
> import Curry.Syntax (Module (..),  Decl (..), parseHeader)

> import Base.ErrorMessages (errCyclicImport, errWrongModule)
> import Base.SCC (scc)
> import CompilerOpts (Options (..), Extension (..))

> data Source
>   = Source FilePath [ModuleIdent]
>   | Interface FilePath
>   | Unknown
>     deriving (Eq, Ord, Show)

> type SourceEnv = Map.Map ModuleIdent Source

> flatDeps :: Options -> FilePath -> IO ([(ModuleIdent, Source)], [String])
> flatDeps opts fn = flattenDeps `liftM` deps opts [] Map.empty fn

> deps :: Options -> [FilePath] -> SourceEnv -> FilePath -> IO SourceEnv
> deps opts paths sEnv fn
>   | ext   ==   icurryExt  = return Map.empty
>   | ext `elem` sourceExts = sourceDeps opts paths sEnv fn
>   | otherwise             = targetDeps opts paths sEnv fn
>   where ext = takeExtension fn

\end{verbatim}
The following functions are used to lookup files related to a given
module. Source files for targets are looked up in the current
directory only. Two different search paths are used to look up
imported modules, the first is used to find source modules, whereas
the library path is used only for finding matching interface files. As
the compiler does not distinguish these paths, we actually check for
interface files in the source paths as well.
\begin{verbatim}

> sourceDeps :: Options -> [FilePath] -> SourceEnv -> FilePath -> IO SourceEnv
> sourceDeps opts paths sEnv fn = do
>   hdr <- (ok . parseHeader fn) `liftM` readModule fn
>   moduleDeps opts paths sEnv fn hdr

> targetDeps :: Options -> [FilePath] -> SourceEnv -> FilePath -> IO SourceEnv
> targetDeps opts paths sEnv fn = do
>   mFile <- lookupFile [""] sourceExts fn
>   case mFile of
>     Nothing   -> return $ Map.insert (mkMIdent [fn]) Unknown sEnv
>     Just file -> sourceDeps opts paths sEnv file

> moduleDeps :: Options -> [FilePath] -> SourceEnv -> FilePath -> Module -> IO SourceEnv
> moduleDeps opts paths sEnv fn (Module m _ ds) = case Map.lookup m sEnv of
>     Just  _ -> return sEnv
>     Nothing -> do
>       let imps  = imports opts m ds
>           sEnv' = Map.insert m (Source fn imps) sEnv
>       foldM (moduleIdentDeps opts paths) sEnv' imps

> -- |Retrieve the imported modules and add the import of the Prelude
> --  according to the compiler options.
> imports :: Options -> ModuleIdent -> [Decl] -> [ModuleIdent]
> imports opts m ds = nub $
>      [preludeMIdent | m /= preludeMIdent && implicitPrelude]
>   ++ [m' | ImportDecl _ m' _ _ _ <- ds]
>   where implicitPrelude = NoImplicitPrelude `notElem` optExtensions opts

\end{verbatim}
In order to compute the dependency graph, source files for each module
need to be looked up. When a source module is found, its header is
parsed in order to determine the modules that it imports, and
dependencies for these modules are computed recursively. The prelude
is added implicitly to the list of imported modules except for the
prelude itself. Any errors reported by the parser are ignored.
\begin{verbatim}

> moduleIdentDeps :: Options -> [FilePath] -> SourceEnv -> ModuleIdent -> IO SourceEnv
> moduleIdentDeps opts paths sEnv m = case Map.lookup m sEnv of
>   Just _  -> return sEnv
>   Nothing -> do
>     mFile <- lookupModule paths libraryPaths m
>     case mFile of
>       Nothing -> return $ Map.insert m Unknown sEnv
>       Just fn
>         | icurryExt `isSuffixOf` fn -> return $ Map.insert m (Interface fn) sEnv
>         | otherwise                 -> checkModuleHeader fn
>   where libraryPaths = optImportPaths opts
>         checkModuleHeader fn = do
>           hdr@(Module m' _ _) <- (ok . parseHeader fn) `liftM` readModule fn
>           unless (m == m') $ error $ errWrongModule m m'
>           moduleDeps opts paths sEnv fn hdr

\end{verbatim}
If we want to compile the program instead of generating Makefile
dependencies the environment has to be sorted topologically. Note
that the dependency graph should not contain any cycles.
\begin{verbatim}

> flattenDeps :: SourceEnv -> ([(ModuleIdent, Source)], [String])
> flattenDeps = fdeps . sortDeps
>   where
>   sortDeps :: SourceEnv -> [[(ModuleIdent, Source)]]
>   sortDeps = scc modules imports' . Map.toList
>
>   modules (m, _) = [m]
>
>   imports' (_, Source _ ms) = ms
>   imports' (_, Interface _) = []
>   imports' (_, Unknown    ) = []
>
>   fdeps :: [[(ModuleIdent, Source)]] -> ([(ModuleIdent, Source)], [String])
>   fdeps = foldr checkdep ([], [])
>
>   checkdep []    (srcs, errs) = (srcs      , errs      )
>   checkdep [src] (srcs, errs) = (src : srcs, errs      )
>   checkdep dep   (srcs, errs) = (srcs      , err : errs)
>     where err = errCyclicImport (map fst dep)

\end{verbatim}
