% -*- LaTeX -*-
% $Id: CCode.lhs,v 1.7 2003/04/29 15:50:13 wlux Exp $
%
% Copyright (c) 2002-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CCode.lhs}
\section{CCode}
The module \texttt{CCode} implements a simplified abstract syntax for 
the C language and functions to pretty print the code. The module 
does not implement the full C syntax but only for the subset of the 
language needed by the Curry compiler. For instance, it is not 
possible to define arbitrary C functions but only functions that can be 
called by the runtime system.
\begin{verbatim}

> module CCode where
> import List
> import Maybe
> infixl 9 `CElem`,`CField`
> infixr 8 `CCast`
> infixl 7 `CMul`,`CDiv`,`CMod`
> infixl 6 `CAdd`,`CSub`
> infixl 5 `CShift`

\end{verbatim}
\subsection{Abstract Syntax Tree}
A C file consists of a sequence of external declarations, variable 
definitions, and function definitions. Conditional compilation of 
declarations can be handled via \texttt{CppCondDecls} which encloses 
its declaration list by \verb|#if| and \verb|#endif| pre-processor 
directives. The string argument is used as argument for the \verb|#if| 
directive. Note that there are no parameters in a function definition 
as the Curry runtime system can only handle such functions.
\begin{verbatim}

> type CFile = [CTopDecl]

> data CTopDecl =
>     CppInclude String
>   | CppCondDecls String [CTopDecl]
>   | CExternVarDecl String String
>   | CExternArrayDecl String String
>   | CEnumDecl [CConst]
>   | CFuncDecl CVisibility String
>   | CVarDef CVisibility String String CInitializer
>   | CArrayDef CVisibility String String [CInitializer]
>   | CFuncDef CVisibility String CBlock
>   | CMainFunc String [String] CBlock
>   deriving Eq

> data CVisibility = CPublic | CPrivate deriving Eq
> data CConst = CConst String (Maybe Int) deriving Eq
> data CInitializer = CInit CExpr | CStruct [CInitializer] deriving Eq

\end{verbatim}
The body of a function consists a list of statements and local 
declarations. We are more liberal than C here in that we allow for an 
arbitrary order of declarations and statements.

Similar to top-level declarations conditional compilation is 
supported through \texttt{CppCondStmts}. Note that there are no 
\texttt{for} and \texttt{while} loops as they are not used by 
the compiler.
\begin{verbatim}

> type CBlock = [CStmt]
> data CStmt =
>     CLocalVar String String (Maybe CExpr)
>   | CStaticArray String String [CInitializer]
>   | CppCondStmts String [CStmt] [CStmt]
>   | CBlock CBlock
>   | CAssign LVar CExpr
>   | CIncrBy LVar CExpr
>   | CDecrBy LVar CExpr
>   | CProcCall String [CExpr]
>   | CIf CExpr [CStmt] [CStmt]
>   | CSwitch CExpr [CCase]
>   | CLoop [CStmt]
>   | CBreak
>   | CContinue
>   | CReturn CExpr
>   | CLabel String
>   | CGoto String
>   | CTrace String [CExpr]
>   deriving Eq

> data LVar = LVar String | LElem LVar CExpr | LField LVar String deriving Eq
> data CCase = CCase String [CStmt] | CDefault [CStmt] deriving Eq

> data CExpr =
>     CInt Int
>   | CFloat Double
>   | CString String
>   | CElem CExpr CExpr
>   | CField CExpr String
>   | CFunCall String [CExpr]
>   | CAdd CExpr CExpr
>   | CSub CExpr CExpr
>   | CMul CExpr CExpr
>   | CDiv CExpr CExpr
>   | CMod CExpr CExpr
>   | CShift CExpr Int
>   | CRel CExpr String CExpr
>   | CAddr CExpr
>   | CCast String CExpr
>   | CExpr String
>   deriving Eq

\end{verbatim}
The function \texttt{mergeCCode} merges the code of two files. In
order to avoid error messages from the C compiler it removes all
duplicate declarations from the resulting file.
\begin{verbatim}

> mergeCFile :: CFile -> CFile -> CFile
> mergeCFile cf1 cf2 = nub (cf1 ++ cf2)

\end{verbatim}
\input{CPretty.lhs}
