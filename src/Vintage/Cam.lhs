% -*- LaTeX -*-
% $Id: Cam.lhs,v 2.8 2004/04/30 01:55:08 wlux Exp $
%
% Copyright (c) 1998-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Cam.lhs}
\section{Abstract Machine Code}
This section describes the instruction set of the abstract machine.
\begin{verbatim}

> module Cam where
> import Char

\end{verbatim}
An abstract machine code module consists of a list of import, data,
and function declarations. A data declaration names the constructors
of a data type together with their arity. A function declaration
comprises the function's name, arguments, and code.
\begin{verbatim}

> type Module = [Decl]
> data Decl =
>     ImportDecl Name
>   | DataDecl Name [ConstrDecl]
>   | FunctionDecl Name [Name] Stmt
>   deriving (Eq,Show)
> data ConstrDecl = ConstrDecl Name Int deriving (Eq,Show)

> splitCam :: Module -> ([Name],[(Name,[ConstrDecl])],[(Name,[Name],Stmt)])
> splitCam = foldr split ([],[],[])
>   where split (ImportDecl m) ~(ms,ds,fs) = (m:ms,ds,fs)
>         split (DataDecl t cs) ~(ms,ds,fs) = (ms,(t,cs):ds,fs)
>         split (FunctionDecl f n is) ~(ms,dss,fs) = (ms,dss,(f,n,is):fs)

\end{verbatim}
\subsection{Instruction Set}
The instruction set of the abstract machine is a simple block
structured language. The body of a function consists of sequence of
statements.

\verb|Return|~$x$ returns the address of the node bound to $x$.

\verb|Enter|~$x$ evaluates the node bound to $x$ to head normal form
and returns its address. If the node is already in head normal form,
\verb|Enter|~$x$ is equivalent to \verb|Return|~$x$.

\verb|Exec|~$f(x_1,\dots,x_k)$ enters the global function $f$ and
passes the nodes referenced by $x_1$, \dots, $x_k$ as arguments to it,
where $k$ is the arity of $f$.

\verb|Switch|~\emph{rf}~$x$~\emph{cases} analyzes the node bound to
$x$ and executes the matching case from \emph{cases}. When $x$ is
bound to a free variable, the current thread is suspended until the
variable is bound if \emph{rf} is \verb|Rigid|, and
non-deterministically instantiated to the patterns of the \emph{cases}
if \emph{rf} is \verb|Flex|.

\verb|Choices|~\emph{alts} non-deterministically executes the
alternatives \emph{alts}.

New nodes are allocated and bound with a \verb|Let|~\emph{binds}
statement. The bindings in a \verb|Let| statement may be mutually
recursive.

Sequencing of statements is implemented with the statement
\verb|Seq|~$x$~\emph{stmt$_1$} \emph{stmt$_2$}. This statement
executes \emph{stmt$_1$} and binds its result to $x$. \emph{stmt$_2$}
is then executed in the extended environment.

The instructions \verb|Lock|~$x$~\emph{stmt} and
\verb|Update|~$x$~$y$~\emph{stmt} are used to the implement the
pattern binding update strategy. The instruction
\verb|Lock|~$x$~\emph{stmt} overwrites the node bound to $x$ with a
queue-me node before executing \emph{stmt} and
\verb|Update|~$x$~$y$~\emph{stmt} overwrites the node bound to $x$
with a pointer to $y$ before executing \emph{stmt}. $x$ must be bound
to a local, unevaluated suspension node for \verb|Lock|, and to a
local queue-me node for \verb|Update|.
\begin{verbatim}

> data Stmt =
>     Return Name
>   | Enter Name
>   | Exec Name [Name]
>   | Lock Name Stmt
>   | Update Name Name Stmt
>   | Seq Name Stmt Stmt
>   | Let [Bind] Stmt
>   | Switch RF Name [Case]
>   | Choices [Alt]
>   deriving (Eq,Show)
> type Alt = Stmt
> data Bind = Bind Name Expr deriving (Eq,Show)
> data RF = Rigid | Flex deriving (Eq,Show)

\end{verbatim}
The abstract machine supports literal constants, data constructors,
function closures (including partial applications), and logic
variables as nodes. As for the STG machine~\cite{Peyton92:STG}, we
distinguish non-updatable \verb|Closure| and updatable \verb|Lazy|
application nodes.

The \verb|Ref|~$x$ expression does not denote a fresh node, but a
reference to the node bound to $x$. An abstract machine program can
always be translated into an equivalent program which does not use
\verb|Ref|s. They are useful during the compilation, though.
\begin{verbatim}

> data Literal = Char Char | Int Int | Float Double deriving (Eq,Show)

> data Expr =
>     Lit Literal
>   | Constr Name [Name]
>   | Closure Name [Name]
>   | Lazy Name [Name]
>   | Free
>   | Ref Name
>   deriving (Eq,Show)

\end{verbatim}
Each case of a switch instruction associates a pattern with a
statement sequence. The pattern is either a literal constant or a data
constructor pattern. In the latter case, the names in the pattern are
bound to the arguments of the data constructor before executing the
statements. A default pattern can be used to match all remaining
cases.
\begin{verbatim}

> data Case = Case Tag Stmt deriving (Eq,Show)
> data Tag = LitCase Literal | ConstrCase Name [Name] | DefaultCase
>            deriving (Eq,Show)

\end{verbatim}
\subsection{External Names}
External names in the abstract machine must be composed of characters
and underscores. Therefore the names of Curry operators have to be
encoded. We use the following strategy for mangling Curry identifiers.
All alpha-numeric characters in an identifier are left unchanged, all
other characters are replaced by a sequence composed of an underscore
character, the (decimal) code of the character, and another underscore
character. As a minor exception from this rule, the dot separating the
module name from the unqualified name in a qualified identifier is
replaced by two consecutive underscores.
\begin{verbatim}

> newtype Name = Name String deriving (Eq,Ord)
> instance Show Name where
>   showsPrec _ (Name name) = showString name

\end{verbatim}
The mangling strategy is implemented by the functions \texttt{mangle}
and \texttt{mangleQualified} below. The inverse operation is
implemented by the function \texttt{demangle}.
\begin{verbatim}

> mangle :: String -> Name
> mangle cs = Name (mangleIdent cs)
>   where mangleIdent [] = []
>         mangleIdent (c:cs)
>           | isAlphaNum c = c : mangleIdent cs
>           | otherwise = '_' : show (ord c) ++ '_' : mangleIdent cs

> mangleQualified :: String -> Name
> mangleQualified cs
>   | null mname = Name name'
>   | otherwise = Name (mname' ++ "__" ++ name')
>   where (mname,name) = splitQualified cs
>         Name mname' = mangle mname
>         Name name'  = mangle name

> demangle :: Name -> String
> demangle (Name cs) = demangleName cs
>   where demangleName [] = []
>         demangleName (c:cs)
>           | c == '_' = unescape ds cs'
>           | otherwise = c : demangleName cs
>           where (ds,cs') = span isDigit cs
>         unescape ds ('_':cs)
>           | null ds = '.' : demangleName cs
>           | n <= ord maxBound = chr n : demangleName cs
>           | otherwise = '_' : ds ++ '_' : demangleName cs
>           where n = read ds
>         unescape ds cs = '_':ds ++ demangleName cs

\end{verbatim}
In order to split a qualified name into its module prefix and the
unqualified name, the function \texttt{splitQualified} assumes that
valid module identifiers have to start with an alphabetic character
and that the unqualified name must not be empty.
\begin{verbatim}

> splitQualified :: String -> (String,String)
> splitQualified [] = ([],[])
> splitQualified (c:cs)
>   | isAlpha c =
>       case break ('.' ==) cs of
>         (_,[]) -> ([],c:cs)
>         (prefix,'.':cs')
>           | null cs' || isDigit (head cs') -> ([],c:cs)
>           | otherwise -> (c:prefix `sep` prefix',name)
>           where (prefix',name) = splitQualified cs'
>                 sep cs1 cs2
>                   | null cs2 = cs1
>                   | otherwise = cs1 ++ '.':cs2
>   | otherwise = ([],c:cs)

\end{verbatim}
\input{CamPP.lhs} % \subsection{Pretty-printing Abstract Machine Code}
\input{CamParser.lhs} % \subsection{Parsing Abstract Machine Code}
