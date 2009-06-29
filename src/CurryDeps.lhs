
% $Id: CurryDeps.lhs,v 1.14 2004/02/09 17:10:05 wlux Exp $
%
% Copyright (c) 2002-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% Extended by Sebastian Fischer (sebf@informatik.uni-kiel.de)
\nwfilename{CurryDeps.lhs}
\section{Building Programs}
This module implements the functions to compute the dependency
information between Curry modules. This is used to create Makefile
dependencies and to update programs composed of multiple modules.
\begin{verbatim}

> module CurryDeps where

> import Data.List
> import Data.Maybe
> import Control.Monad

> import Curry.Syntax.ParseResult
> import Ident
> import Unlit
> import Curry.Syntax hiding(Interface(..))
> import Curry.Syntax.Parser(parseHeader)
> import SCC
> import Env

> import PathUtils

> data Source = Source FilePath [ModuleIdent]
>             | Interface FilePath
>             | Unknown
>             deriving (Eq,Ord,Show)
> type SourceEnv = Env ModuleIdent Source

\end{verbatim}
The module has two entry points. The function \texttt{buildScript}
computes either a build or clean script for a module while
\texttt{makeDepend} computes dependency rules for inclusion into a
Makefile.
\begin{verbatim}

> buildScript :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
>             -> [FilePath] -> [FilePath] -> Maybe FilePath -> FilePath 
>             -> IO [String]
> buildScript clean debug linkAlways flat xml acy uacy
>             paths libraryPaths ofn fn =
>   do
>     mfn'      <- getCurryPath (paths ++ libraryPaths) fn
>     (fn',es1) <- return (maybe ("",["Error: missing module \"" ++ fn ++ "\""])
>                                (\x -> (x,[]))
>                                mfn')
>     (ms,es2)  <- fmap 
>                   (flattenDeps . sortDeps)
>                   (deps paths (filter (`notElem` paths) libraryPaths) emptyEnv fn')
>     es        <- return (es1 ++ es2)
>     when (null es)
>          (putStr 
>            (makeScript clean debug flat xml acy uacy linkAlways 
>                        (outputFile fn') fn ms))
>     return es
>   where outputFile fn
>           | takeExtension fn `elem` moduleExts ++ objectExts = Nothing
>           | otherwise = ofn `mplus` Just fn
>         makeScript clean = if clean then makeCleanScript else makeBuildScript

> makeDepend :: [FilePath] -> [FilePath] -> Maybe FilePath -> [FilePath]
>            -> IO ()
> makeDepend paths libraryPaths ofn ms =
>   do
>     flatDeps <- liftM (makeDeps True) (allDeps flat)
>     objectDeps <- liftM (makeDeps False) (allDeps nonFlat)
>     maybe putStr writeFile ofn (flatDeps ++ objectDeps)
>   where (flat,nonFlat) = partition (flatExt `isSuffixOf`) ms
>         allDeps = foldM (deps paths libraryPaths') emptyEnv
>         libraryPaths' = filter (`notElem` paths) libraryPaths

> deps :: [FilePath] -> [FilePath] -> SourceEnv -> FilePath -> IO SourceEnv
> deps paths libraryPaths mEnv fn
>   | e `elem` sourceExts = sourceDeps paths libraryPaths (mkMIdent [r]) mEnv fn
>   | e == icurryExt = return emptyEnv
>   | e `elem` objectExts = targetDeps paths libraryPaths mEnv r
>   | otherwise = targetDeps paths libraryPaths mEnv fn
>   where r = dropExtension fn
>         e = takeExtension fn

> targetDeps :: [FilePath] -> [FilePath] -> SourceEnv -> FilePath
>            -> IO SourceEnv
> targetDeps paths libraryPaths mEnv fn =
>   lookupFile [""] sourceExts fn >>=
>   maybe (return (bindEnv m Unknown mEnv)) (sourceDeps paths libraryPaths m mEnv)
>   where m = mkMIdent [fn]

\end{verbatim}
The following functions are used to lookup files related to a given
module. Source files for targets are looked up in the current
directory only. Two different search paths are used to look up
imported modules, the first is used to find source modules, whereas
the library path is used only for finding matching interface files. As
the compiler does not distinguish these paths, we actually check for
interface files in the source paths as well.

Note that the functions \texttt{buildScript} and \texttt{makeDepend}
already remove all directories that are included in the both search
paths from the library paths in order to avoid scanning such
directories more than twice.
\begin{verbatim}

> lookupModule :: [FilePath] -> [FilePath] -> ModuleIdent
>              -> IO (Maybe FilePath)
> lookupModule paths libraryPaths m
>     = lookupFile ("" : paths ++ libraryPaths) moduleExts fn
>     where fn = foldr1 catPath (moduleQualifiers m)

\end{verbatim}
In order to compute the dependency graph, source files for each module
need to be looked up. When a source module is found, its header is
parsed in order to determine the modules that it imports, and
dependencies for these modules are computed recursively. The prelude
is added implicitly to the list of imported modules except for the
prelude itself. Any errors reported by the parser are ignored.
\begin{verbatim}

> moduleDeps :: [FilePath] -> [FilePath] -> SourceEnv -> ModuleIdent
>            -> IO SourceEnv
> moduleDeps paths libraryPaths mEnv m =
>   case lookupEnv m mEnv of
>     Just _ -> return mEnv
>     Nothing ->
>       do
>         mbFn <- lookupModule paths libraryPaths m
>         case mbFn of
>           Just fn
>             | icurryExt `isSuffixOf` fn ->
>                 return (bindEnv m (Interface fn) mEnv)
>             | otherwise -> sourceDeps paths libraryPaths m mEnv fn
>           Nothing -> return (bindEnv m Unknown mEnv)

> sourceDeps :: [FilePath] -> [FilePath] -> ModuleIdent -> SourceEnv
>            -> FilePath -> IO SourceEnv
> sourceDeps paths libraryPaths m mEnv fn =
>   do
>     s <- readModule fn
>     case parseHeader fn (unlitLiterate fn s) of
>       Ok (Module m' _ ds) ->
>         let ms = imports m' ds in
>         foldM (moduleDeps paths libraryPaths) (bindEnv m (Source fn ms) mEnv) ms
>       Error _ -> return (bindEnv m (Source fn []) mEnv)

> imports :: ModuleIdent -> [Decl] -> [ModuleIdent]
> imports m ds = nub $
>   [preludeMIdent | m /= preludeMIdent] ++ [m | ImportDecl _ m _ _ _ <- ds]

> unlitLiterate :: FilePath -> String -> String
> unlitLiterate fn
>   | lcurryExt `isSuffixOf` fn = snd . unlit fn
>   | otherwise = id

\end{verbatim}
It is quite straight forward to generate Makefile dependencies from
the dependency environment. In order for these dependencies to work,
the Makefile must include a rule
\begin{verbatim}
.SUFFIXES: .lcurry .curry .icurry
.o.icurry: @echo interface $@ not found, remove $< and recompile; exit 1
\end{verbatim}
This dependency rule introduces an indirect dependency between a
module and its interface. In particular, the interface may be updated
when the module is recompiled and a new object file is generated but
it does not matter if the interface is out-of-date with respect to the
object code.
\begin{verbatim}

> makeDeps :: Bool -> SourceEnv -> String
> makeDeps flat mEnv =
>   unlines (filter (not . null) (map (depsLine . snd) (envToList mEnv)))
>   where depsLine (Source fn ms) =
>           targetName fn ++ ": " ++ fn ++ " " ++
>           unwords (filter (not . null) (map interf ms))
>         depsLine (Interface _) = []
>         depsLine Unknown = []
>         interf m = maybe [] interfFile (lookupEnv m mEnv)
>         interfFile (Source fn _) = interfName fn
>         interfFile (Interface fn) = fn
>         interfFile Unknown = ""
>         targetName = if flat then flatName else objectName False

\end{verbatim}
If we want to compile the program instead of generating Makefile
dependencies the environment has to be sorted topologically. Note
that the dependency graph should not contain any cycles.
\begin{verbatim}

> sortDeps :: SourceEnv -> [[(ModuleIdent,Source)]]
> sortDeps = scc (modules . fst) (imports . snd) . envToList
>   where modules m = [m]
>         imports (Source _ ms) = ms
>         imports (Interface _) = []
>         imports Unknown = []

> flattenDeps :: [[(ModuleIdent,Source)]] -> ([(ModuleIdent,Source)],[String])
> flattenDeps [] = ([],[])
> flattenDeps (dep:deps) =
>   case dep of
>     [] -> (ms',es')
>     [m] -> (m:ms',es')
>     _ -> (ms',cyclicError (map fst dep) : es')
>   where (ms',es') = flattenDeps deps

> cyclicError :: [ModuleIdent] -> String
> cyclicError (m:ms) =
>   "Cylic import dependency between modules " ++ show m ++ rest ms
>   where rest [m] = " and " ++ show m
>         rest (m:ms) = ", " ++ show m ++ rest' ms
>         rest' [m] = ", and " ++ show m
>         rest' (m:ms) = ", " ++ show m ++ rest' ms

\end{verbatim}
The function \texttt{makeBuildScript} returns a shell script that
rebuilds several program representations (e.g. interfaces, FlatCurry etc.)
given a sorted list of module informations. The
script uses the command \verb|compile| and \verb|link| to build
programs and representations. They should be defined to reasonable values in the
environment where the script is executed (e.g. compile=cyc
The script deliberately uses
the \verb|-e| shell option so that the script is terminated upon the
first error. Unlike the original function \texttt{makeBuildScript} this
modification uses the command "smake" to check the out-of-dateness
of dependend program files.
\begin{verbatim}

> makeBuildScript :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool 
>                 -> Maybe FilePath -> FilePath -> [(ModuleIdent,Source)] 
>                 -> String
> makeBuildScript debug flat xml acy uacy linkAlways ofn fn mEnv =
>   unlines ("set -e" : (map (compCommands . snd) mEnv)
>                       ++ (maybe [] linkCommands ofn))
>   where 
>         compCommands (Source fn' ms)
>            | (acy || uacy) && dropExtension fn /= dropExtension fn'
>              = (smake ([flatName fn', flatIntName fn'])
>                       (fn' : catMaybes (map flatInt ms))
>                       "")
>                ++ " || (\\" --rm -f " ++ (interfName fn') ++ " && \\"
>                ++ unwords ["compile", "--flat", fn', "-o",
>                            flatName fn']
>                ++ ")"
>            | otherwise
>              = (smake (targetNames fn')
>                       (fn' : catMaybes (map flatInt ms))
>                       "")
>                ++ " || (\\" --rm -f " ++ (interfName fn')
>                ++ (compile fn') ++ ")"
>         compCommands (Interface _) = []
>         compCommands Unknown = []
>
>         linkCommands fn'
>           | linkAlways = [link fn' os]
>           | otherwise  = [smake [fn'] os "", " || \\", (link fn' os)]
>           where os = reverse (catMaybes (map (object . snd) mEnv))
>
>         smake ts ds rule
>            = "$CURRY_PATH/smake " 
>              ++ (unwords ts) ++ " : " 
>              ++ (unwords ds)
>              ++ (if null rule then "" else " : " ++ rule)
>
>         compile fn' = unwords ["compile", cFlag, fn', "-o", 
>                                head (targetNames fn')] 
>
>         cFlag | flat      = "--flat"
>               | xml       = "--xml"
>               | acy       = "--acy"
>               | uacy      = "--uacy"
>               | otherwise = "-c"
>
>         oGen fn' | flat || xml || acy || uacy = []
>                  | otherwise   = ["-o", head (targetNames fn')]
>
>         link fn' os = unwords ("link" : "-o" : fn' : os)
>
>         flatInt m =
>           case lookup m mEnv of
>             Just (Source fn' _) 
>	        -> Just (flatIntName fn')
>             Just (Interface fn') 
>	        -> Just (flatIntName (takeBaseName fn'))
>             Just Unknown 
>	        -> Nothing
>             _ -> Nothing
>
>         object (Source fn' _) = Just (head (targetNames fn'))
>         object (Interface _) = Nothing
>         object Unknown = Nothing
>
>         targetNames fn' | flat      = [flatName fn', flatIntName fn']
>                         | xml       = [xmlName fn']
>                         | acy       = [acyName fn']
>                         | uacy      = [uacyName fn']
>                         | otherwise = [objectName debug fn']


\end{verbatim}
The function \texttt{makeCleanScript} returns a shell script that
removes all compiled files for a module. The script uses the command
\verb|remove| to delete the files. It should be defined to a
reasonable value in the environment where the script is executed.
\begin{verbatim}

> makeCleanScript :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool 
>                 -> Maybe FilePath -> FilePath -> [(ModuleIdent,Source)] 
>                 -> String
> makeCleanScript debug flat xml acy uacy _ ofn _ mEnv =
>   unwords ("remove" : foldr files (maybe [] return ofn) (map snd mEnv))
>   where d = if debug then 2 else 0
>         files = if flat then flatFiles else nonFlatFiles
>         flatFiles (Source fn _) fs =
>           drop d [interfName fn,flatName fn] ++ fs
>         flatFiles (Interface _) fs = fs
>         flatFiles Unknown fs = fs
>         nonFlatFiles (Source fn _) fs =
>           drop d [interfName fn,objectName False fn,objectName True fn] ++
>           fs
>         nonFlatFiles (Interface _) fs = fs
>         nonFlatFiles Unknown fs = fs

\end{verbatim}
The function \verb|getCurryPath| searches in predefined paths
for the corresponding \texttt{.curry} or \texttt{.lcurry} file, 
if the given file name has no extension.
\begin{verbatim}

> getCurryPath :: [FilePath] -> FilePath -> IO (Maybe FilePath)
> getCurryPath paths fn
>   = lookupFile filepaths exts fn
>  where
>  filepaths = "":paths'
>  fnext = takeExtension fn
>  exts | null fnext = sourceExts
>       | otherwise  = [fnext]
>  paths' | pathSeparator `elem` fn = []
>         | otherwise               = paths


\end{verbatim}
The following functions compute the name of the target file (e.g.
interface file, flat curry file etc.)
for a source module. Note that
output files are always created in the same directory as the source
file.
\begin{verbatim}

> interfName :: FilePath -> FilePath
> interfName sfn = replaceExtension sfn icurryExt

> flatName :: FilePath -> FilePath
> flatName fn = replaceExtension fn flatExt

> flatIntName :: FilePath -> FilePath
> flatIntName fn = replaceExtension fn flatIntExt

> xmlName :: FilePath -> FilePath
> xmlName fn = replaceExtension fn xmlExt

> acyName :: FilePath -> FilePath
> acyName fn = replaceExtension fn acyExt

> uacyName :: FilePath -> FilePath
> uacyName fn = replaceExtension fn uacyExt

> sourceRepName :: FilePath -> FilePath
> sourceRepName fn = replaceExtension fn sourceRepExt

> objectName :: Bool -> FilePath -> FilePath
> objectName debug = name (if debug then debugExt else oExt)
>   where name ext fn = replaceExtension fn ext

> curryExt, lcurryExt, icurryExt, oExt :: String
> curryExt = ".curry"
> lcurryExt = ".lcurry"
> icurryExt = ".icurry"
> flatExt = ".fcy"
> flatIntExt = ".fint"
> xmlExt = "_flat.xml"
> acyExt = ".acy"
> uacyExt = ".uacy"
> sourceRepExt = ".cy"
> oExt = ".o"
> debugExt = ".d.o"

> sourceExts, moduleExts, objectExts :: [String]
> sourceExts = [curryExt,lcurryExt]
> moduleExts = sourceExts ++ [icurryExt]
> objectExts = [oExt]

\end{verbatim}
