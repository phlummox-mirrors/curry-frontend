% -*- LaTeX -*-
% $Id: Options.lhs,v 1.12 2003/05/23 21:12:46 wlux Exp $
%
% Copyright (c) 2001-2003, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified in March 2005,
% Martin Engelke (men@informatik.uni-kiel.de)
\nwfilename{Options.lhs}
\section{Compiler options}
\begin{verbatim}

> module Options where
> import GetOpt

\end{verbatim}
A record of type \texttt{Options} is used to gather the settings of
all compiler options.
\begin{verbatim}

> data Options =
>   Options {
>     importPath :: [FilePath],         -- directories for searching imports
>     output :: Maybe FilePath,         -- name of output file
>     goal :: Maybe (Maybe String),     -- goal to be evaluated
>     typeIt :: Maybe String,           -- goal to be typed
>     noInterface :: Bool,              -- do not create an interface file
>     flatXML :: Bool,                  -- generate flat XML code
>     flatCurry :: Bool,                -- emit flat curry instead of C code
>     abstractCurry :: Bool,            -- generate abstract curry code
>     splitCode :: Bool,                -- split C code
>     debug :: Bool,                    -- add debugging transformation
>     trusted :: Bool,                  -- trusted module for debugging
>     dump :: [Dump]                    -- dumps
>   }
>   deriving Show

> defaultOptions =
>   Options{
>     importPath = [],
>     output = Nothing,
>     goal = Nothing,
>     typeIt = Nothing,
>     noInterface = False,
>     flatXML = False,
>     flatCurry = False,
>     abstractCurry = False,
>     splitCode = False,
>     debug = False,
>     trusted = False,
>     dump = []
>   }

> data Dump =
>     DumpRenamed                       -- dump source after renaming
>   | DumpTypes                         -- dump types after typechecking
>   | DumpDesugared                     -- dump source after desugaring
>   | DumpSimplified                    -- dump source after simplification
>   | DumpLifted                        -- dump source after lambda-lifting
>   | DumpIL                            -- dump IL code after translation
>   | DumpTransformed                   -- dump transformed code
>   | DumpNormalized                    -- dump IL code after normalization
>   | DumpCam                           -- dump abstract machine code
>   deriving (Eq,Bounded,Enum,Show)

\end{verbatim}
The \texttt{Option} type maps every command line switch on a data
constructor. This is needed in order to use the \texttt{GetOpt}
library.
\begin{verbatim}

> data Option =
>     Help
>   | ImportPath FilePath | Output FilePath
>   | Eval (Maybe String) | Type String
>   | SplitCode | NoInterface 
>   | FlatXML | Flat | Abstract | Debug | Trusted | Dump [Dump]
>   deriving (Eq,Show)

\end{verbatim}
The global variable \texttt{options} defines all options which are
recognized by the compiler.
\begin{verbatim}

> options = [
>     Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
>            "search for imports in DIR",
>     Option "e" ["eval"] (OptArg Eval "GOAL")
>            "generate code to evaluate GOAL",
>     Option "t" ["type"] (ReqArg Type "GOAL")
>            "print type of GOAL",
>     Option "o" ["output"] (ReqArg Output "FILE")
>            "write code to FILE",
>     Option "" ["no-icurry"] (NoArg NoInterface)
>            "do not create an interface file",
>     Option "" ["xml"] (NoArg FlatXML)
>            "generate flat xml code instead of C code",
>     Option "" ["flat"] (NoArg Flat)
>            "emit flat curry instead of C code",
>     Option "" ["abstract"] (NoArg Abstract)
>            "generate abstract curry code instead of C code",
>     Option "" ["split-code"] (NoArg SplitCode)
>            "emit one C file for each function",
>     Option "g" ["debug"] (NoArg Debug)
>            "transform code for debugging",
>     Option "" ["trusted"] (NoArg Trusted)
>            "trust this module (if compiled with -g/--debug)",
>     Option "" ["dump-all"] (NoArg (Dump [minBound..maxBound]))
>            "dump everything",
>     Option "" ["dump-renamed"] (NoArg (Dump [DumpRenamed]))
>            "dump source code after renaming",
>     Option "" ["dump-types"] (NoArg (Dump [DumpTypes]))
>            "dump types after type-checking",
>     Option "" ["dump-desugared"] (NoArg (Dump [DumpDesugared]))
>            "dump source code after desugaring",
>     Option "" ["dump-simplified"] (NoArg (Dump [DumpSimplified]))
>            "dump source code after simplification",
>     Option "" ["dump-lifted"] (NoArg (Dump [DumpLifted]))
>            "dump source code after lambda-lifting",
>     Option "" ["dump-il"] (NoArg (Dump [DumpIL]))
>            "dump intermediate language before lifting",
>     Option "" ["dump-transformed"] (NoArg (Dump [DumpTransformed]))
>            "dump IL code after debugging transformation",
>     Option "" ["dump-normalized"] (NoArg (Dump [DumpNormalized]))
>            "dump IL code after normalization",
>     Option "" ["dump-cam"] (NoArg (Dump [DumpCam]))
>            "dump abstract machine code",
>     Option "?h" ["help"] (NoArg Help)
>            "display this help and exit"
>   ]

\end{verbatim}
The function \texttt{selectOption} applies an \texttt{Option} to an
\texttt{Options} record. Note that there is no case for
\texttt{Help}. If the user asks for help, the compiler will simply
print its usage message and terminate.
\begin{verbatim}

> selectOption :: Option -> Options -> Options
> selectOption (ImportPath dir) opts =
>   opts{ importPath = dir : importPath opts }
> selectOption (Output file) opts = opts{ output = Just file }
> selectOption (Eval goal) opts = opts{ goal = Just goal }
> selectOption (Type goal) opts = opts{ typeIt = Just goal }
> selectOption NoInterface opts = opts{ noInterface = True }
> selectOption FlatXML opts = opts{ flatXML = True }
> selectOption Flat opts = opts{ flatCurry = True }
> selectOption Abstract opts = opts{ abstractCurry = True }
> selectOption SplitCode opts = opts{ splitCode = True }
> selectOption Debug opts = opts{ debug = True }
> selectOption Trusted opts = opts{ trusted = True }
> selectOption (Dump ds) opts = opts{ dump = ds ++ dump opts }

\end{verbatim}
