% -*- LaTeX -*-
% $Id: CPretty.lhs,v 1.8 2004/04/21 21:24:18 wlux Exp $
%
% Copyright (c) 2002-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPretty.lhs}
\subsection{Pretty-Printing}
The module \texttt{CPretty} implements a pretty printer for the
abstract C syntax tree. Actually, the generated code is not really
pretty, but this module has been tuned towards efficienct code
generation. If you want prettier code, run the code through a C
program formatter.\footnote{For instance, on Unix systems
\texttt{indent(1)} can be used for that purpose.}
\begin{verbatim}

> module CPretty where

> import CCode
> import PrettyCombinators
> import List

> ppCFile :: CFile -> Doc
> ppCFile = vsep . map ppTopDecl

> ppTopDecl :: CTopDecl -> Doc
> ppTopDecl (CppInclude f) = text "#include" <+> string f
> ppTopDecl (CppCondDecls c ds)
>   | null ds = empty
>   | otherwise =
>       text "#if" <+> text c $+$
>       vsep (map ppTopDecl ds) $+$
>       text "#endif"
> ppTopDecl (CExternVarDecl ty v) = text "extern" <+> varDecl ty v <> semi
> ppTopDecl (CExternArrayDecl ty v) = text "extern" <+> arrayDecl ty v <> semi
> ppTopDecl (CEnumDecl cs)
>   | null cs = empty
>   | otherwise =
>       text "enum" $+$ block (punctuate comma (map ppConst cs)) <> semi
> ppTopDecl (CFuncDecl vb f) = ppFunCall (decl vb) [text f] <> semi
>   where decl CPublic = "DECLARE_ENTRYPOINT"
>         decl CPrivate = "DECLARE_LABEL"
> ppTopDecl (CVarDef vb ty v (CInit x)) =
>   ppVisi vb <+> varDecl ty v <> equals <> ppExpr 0 x <> semi
> ppTopDecl (CVarDef vb ty v (CStruct xs)) =
>   ppVisi vb <+> varDecl ty v <> equals $+$ ppInits xs <> semi
> ppTopDecl (CArrayDef vb ty v xs) =
>   ppVisi vb <+> arrayDecl ty v <> equals $+$ ppInits xs <> semi
> ppTopDecl (CFuncDef vb f sts) =
>   ppVisi vb <+> ppFunCall "FUNCTION" [text f] $+$
>   ppBlock (exportLabel vb f $+$ entryLabel f) sts
>   where entryLabel f = ppFunCall "ENTRY_LABEL" [text f]
>         exportLabel CPublic f = ppFunCall "EXPORT_LABEL" [text f]
>         exportLabel CPrivate _ = empty
> ppTopDecl (CMainFunc f xs sts) =
>   ppVisi CPublic <+> text "int" <+>
>     ppFunCall f (zipWith varDecl ["int","char **","char **"] xs) $+$
>   ppBlock empty sts

> ppVisi :: CVisibility -> Doc
> ppVisi CPublic = empty
> ppVisi CPrivate = text "static"

> ppConst :: CConst -> Doc
> ppConst (CConst c x) = text c <> maybe empty (\i -> equals <> int i) x

> ppInits :: [CInitializer] -> Doc
> ppInits xs = block (punctuate comma (map ppInit xs))

> ppInit :: CInitializer -> Doc
> ppInit (CInit x) = ppExpr 0 x
> ppInit (CStruct xs) = braces $ hcat $ punctuate comma (map ppInit xs)

\end{verbatim}
When a code block is printed, the compiler filters out its
local declarations and emits them at the beginning of the
block. Before emitting the statements, the function \texttt{ppBlock}
can insert an arbitrary code sequence. This is used to insert the
entry-label into a function block. For nested blocks no additional
code has to be inserted. As all code before the entry-point is skipped
when using the direct jump model, \texttt{ppBlock} replaces the
declarations by assignments for the declared variables at the place
where they occur in the block.

Multiple declarations for the same local variable are permitted and 
merged into a single declaration. Thus, the C code generator can use 
generic names like \texttt{retIp} in the code without having to check 
whether a declaration for the variable is present in the code already.
\begin{verbatim}

> ppBlock :: Doc -> CBlock -> Doc
> ppBlock entry sts = block (map ppDecl ds ++ entry : map ppStmt sts)
>   where ds = nubBy sameVar (foldr collectDecl [] sts)
>         sameVar (CLocalVar ty1 v1 _) (CLocalVar ty2 v2 _) =
>           ty1 == ty2 && v1 == v2
>         sameVar _ _ = False

> ppNestedBlock :: CBlock -> Doc
> ppNestedBlock = ppBlock empty

> collectDecl :: CStmt -> [CStmt] -> [CStmt]
> collectDecl (CLocalVar ty v _) ds = CLocalVar ty v Nothing : ds
> collectDecl (CStaticArray ty v xs) ds = CStaticArray ty v xs : ds
> collectDecl (CppCondStmts _ sts1 sts2) ds =
>   foldr collectDecl ds (sts1 ++ sts2)
> collectDecl _ ds = ds

> ppDecl :: CStmt -> Doc
> ppDecl (CLocalVar ty v _) = varDecl ty v <> semi
> ppDecl (CStaticArray ty v xs) = ppTopDecl (CArrayDef CPrivate ty v xs)

\end{verbatim}
The printer ensures that every statement will start on a new line.
This is necessary in order to emit C-preprocessor directives without
checking for the current indentation.
\begin{verbatim}

> ppStmts :: [CStmt] -> Doc
> ppStmts = vsep . map ppStmt

> ppStmt :: CStmt -> Doc
> ppStmt (CLocalVar _ v x) = maybe empty (ppStmt . CAssign (LVar v)) x
> ppStmt (CStaticArray _ _ _) = empty
> ppStmt (CppCondStmts c sts1 sts2) =
>   text "#if" <+> text c $+$ ppStmts sts1 $+$ ppElse sts2 $+$ text "#endif"
>   where ppElse sts = if null sts then empty else text "#else" $+$ ppStmts sts
> ppStmt (CBlock sts) = ppNestedBlock sts
> ppStmt (CAssign x y) = ppLhs x <> equals <> ppExpr 0 y <> semi
> ppStmt (CIncrBy x y) = ppLhs x <> text "+=" <> ppExpr 0 y <> semi
> ppStmt (CDecrBy x y) = ppLhs x <> text "-=" <> ppExpr 0 y <> semi
> ppStmt (CProcCall f xs) = ppFunCall f (map (ppExpr 0) xs) <> semi
> ppStmt (CIf c sts1 sts2) =
>   text "if" <> parens (ppExpr 0 c) $+$ ppNestedBlock sts1 $+$ ppElse sts2
>   where ppElse sts =
>           case sts of
>             [] -> empty
>             [CIf c sts1 sts2] ->
>               text "else if" <> parens (ppExpr 0 c) $+$
>               ppNestedBlock sts1 $+$
>               ppElse sts2
>             _ -> text "else" $+$ ppNestedBlock sts
> ppStmt (CSwitch e cases) =
>   text "switch" <> parens (ppExpr 0 e) $+$ block (map ppCase cases)
> ppStmt (CLoop sts) = text "for(;;)" $+$ ppNestedBlock sts
> ppStmt CBreak = text "break" <> semi
> ppStmt CContinue = text "continue" <> semi
> ppStmt (CReturn e) = text "return" <+> ppExpr 0 e <> semi
> ppStmt (CLabel l) = text l <> colon
> ppStmt (CGoto l) = text "goto" <+> text l <> semi
> ppStmt (CTrace fmt xs) = 
>   ppFunCall "TRACE" [parens (hcat (punctuate comma args))] <> semi
>   where args = map (ppExpr 0) (CString fmt : xs)

> ppLhs :: LVar -> Doc
> ppLhs (LVar x) = text x
> ppLhs (LElem x i) = ppLhs x <> brackets (ppExpr 0 i)
> ppLhs (LField x f) = ppLhs x <> text "->" <> text f

\end{verbatim}
If the statement sequence following a case label contains any
declarations, the compiler automatically encloses the statements in a
nested block.
\begin{verbatim}

> ppCase :: CCase -> Doc
> ppCase (CCase c sts) = text "case" <+> text c <> colon $+$ ppCaseStmts sts
> ppCase (CDefault sts) = text "default" <> colon $+$ ppCaseStmts sts

> ppCaseStmts :: [CStmt] -> Doc
> ppCaseStmts sts = if null ds then ppStmts sts else ppStmt (CBlock sts)
>   where ds = foldr collectDecl [] sts

\end{verbatim}
The expression printer uses a precedence level in order to insert
parentheses around sub-expressions when this is necessary. This code
does not attempt to implement the full precedence hierarchy of ANSI C,
but uses a subset that is suitable for printing the expressions
generated by the compiler.

Note that a negative integer literal $l$ is replaced by an expression
$l'-1$, where $l'=l+1$. This avoids a C compiler warning ``decimal
constant is so large that it is unsigned'' when the largest possible
negative integer ($-2^{31}$ on a 32-bit architecture and $-2^{63}$ on
a 64-bit architecture) is emitted without actually knowing the target
architecture's word size.
\begin{verbatim}

> ppExpr :: Int -> CExpr -> Doc
> ppExpr p (CInt i)
>   | i < 0 = ppParens (p > 2) $ int (i + 1) <> text "-1"
>   | otherwise = int i
> ppExpr _ (CFloat f) = double f
> ppExpr _ (CString s) = string s
> ppExpr _ (CElem x i) = ppExpr 5 x <> brackets (ppExpr 0 i)
> ppExpr _ (CField x f) = ppExpr 5 x <> text "->" <> text f
> ppExpr _ (CFunCall f xs) = ppFunCall f (map (ppExpr 0) xs)
> ppExpr p (CAdd x y) =
>   ppParens (p > 2) $ ppExpr 2 x <> text "+" <> ppExpr 2 y
> ppExpr p (CSub x y) =
>   ppParens (p > 2) $ ppExpr 2 x <> text "-" <> ppExpr 3 y
> ppExpr p (CMul x y) =
>   ppParens (p > 3) $ ppExpr 3 x <> text "*" <> ppExpr 3 y
> ppExpr p (CDiv x y) =
>   ppParens (p > 3) $ ppExpr 3 x <> text "/" <> ppExpr 4 y
> ppExpr p (CMod x y) =
>   ppParens (p > 3) $ ppExpr 3 x <> text "%" <> ppExpr 4 y
> ppExpr p (CShift x n)
>   | n > 0 = ppParens (p > 1) $ ppExpr 1 x <> text "<<" <> int n
>   | otherwise = ppParens (p > 1) $ ppExpr 1 x <> text ">>" <> int (-n)
> ppExpr p (CRel x rel y) =
>   ppParens (p > 0) $ ppExpr 1 x <> text rel <> ppExpr 1 y
> ppExpr p (CAddr x) = ppParens (p > 4) $ char '&' <> ppExpr 4 x
> ppExpr p (CCast ty x) = ppParens (p > 4) $ parens (text ty) <> ppExpr 4 x
> ppExpr _ (CExpr x) = text x

> ppParens :: Bool -> Doc -> Doc
> ppParens b = if b then parens else id

> ppFunCall :: String -> [Doc] -> Doc
> ppFunCall f xs = text f <> parens (hcat $ punctuate comma xs)

> block :: [Doc] -> Doc
> block xs = vsep (lbrace : xs ++ [rbrace])

> varDecl, arrayDecl :: String -> String -> Doc
> varDecl ty v = text ty <+> text v
> arrayDecl ty v = varDecl ty v <> brackets empty

> string :: String -> Doc
> string = text . show

> vsep :: [Doc] -> Doc
> vsep = foldr ($+$) empty

\end{verbatim}
