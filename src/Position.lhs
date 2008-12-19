% -*- LaTeX -*-
% $Id: Position.lhs,v 1.2 2000/10/08 09:55:43 lux Exp $
%
% $Log: Position.lhs,v $
% Revision 1.2  2000/10/08 09:55:43  lux
% Column numbers now start at 1. If the column number is less than 1 it
% will not be shown.
%
% Revision 1.1  2000/07/23 11:03:37  lux
% Positions now implemented in a separate module.
%
%
\nwfilename{Position.lhs}
\section{Positions}
A source file position consists of a filename, a line number, and a
column number. A tab stop is assumed at every eighth column.
\begin{verbatim}

> module Position where

> data Position =
>   Position{ file :: FilePath, line :: Int, column :: Int }
>   deriving (Eq, Ord)

> instance Read Position where
>   readsPrec p s = 
>     [ (Position{file="",line=i,column=j},s')  | ((i,j),s') <- readsPrec p s]

> instance Show Position where
>   showsPrec _ (Position fn l c) =
>     (if null fn then id else shows fn . showString ", ") .
>     showString "line " . shows l .
>     (if c > 0 then showChar '.' . shows c else id)

> tabWidth :: Int
> tabWidth = 8

> first :: FilePath -> Position
> first fn = Position fn 1 1

> incr :: Position -> Int -> Position
> incr (Position fn l c) n = Position fn l (c + n)

> next :: Position -> Position
> next = flip incr 1

> tab :: Position -> Position
> tab (Position fn l c) = Position fn l (c + tabWidth - (c - 1) `mod` tabWidth)

> nl :: Position -> Position
> nl (Position fn l c) = Position fn (l + 1) 1

> noPos :: Position
> noPos = Position{ file = "", line = 0, column = 0 }

> showLine :: Position -> String
> showLine x@(Position _ l c) 
>      | x == noPos = ""
>      | otherwise = "(line " ++ show l ++ "." ++ show c ++ ") "

\end{verbatim}
