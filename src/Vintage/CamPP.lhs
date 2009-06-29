% -*- LaTeX -*-
% $Id: CamPP.lhs,v 2.8 2004/04/30 01:55:08 wlux Exp $
%
% Copyright (c) 2002-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\subsection{Pretty-printing Abstract Machine Code}
\begin{verbatim}

> module CamPP where
> import Cam
> import Char
> import PrettyCombinators

> default(Int)

> blockIndent = 2

> ppModule :: Module -> Doc
> ppModule ds = vcat $ punctuate semi $ map ppDecl ds

> ppDecl :: Decl -> Doc
> ppDecl (ImportDecl m) = ppKW "import" <+> ppName m
> ppDecl (DataDecl t cs) =
>   ppKW "data" <+> ppName t
>               <+> sep (zipWith (<+>) (equals : repeat bar) (map ppConstr cs))
>   where ppConstr (ConstrDecl c n) = ppName c <> char '/' <> int n
> ppDecl (FunctionDecl f vs is) =
>   ppCode (ppKW "function" <+> ppName f <> ppNames vs) is

> ppCode :: Doc -> Stmt -> Doc
> ppCode prefix = ppBlock prefix . ppStmt

> ppBlock :: Doc -> Doc -> Doc
> ppBlock prefix x = sep [prefix <+> lbrace,nest blockIndent x,rbrace]

> ppStmt :: Stmt -> Doc
> ppStmt (Return v) = ppKW "return" <+> ppName v
> ppStmt (Enter v) = ppKW "enter" <+> ppName v
> ppStmt (Exec f vs) = ppKW "exec" <+> ppName f <> ppNames vs
> ppStmt (Lock v st) = ppSeq (ppKW "lock" <+> ppName v) st
> ppStmt (Update v1 v2 st) =
>   ppSeq (ppKW "update" <+> ppName v1 <+> ppName v2) st
> ppStmt (Seq v st1 st2) =
>   ppSeq (ppCall (ppName v <+> text "<-") (ppStmt st1)) st2
>   where ppCall = if needsBlock st1 then ppBlock else (<+>)
>         needsBlock (Return _) = False
>         needsBlock (Enter _) = False
>         needsBlock (Exec _ _) = False
>         needsBlock (Lock _ _) = True
>         needsBlock (Update _ _ _) = True
>         needsBlock (Seq _ _ _) = True
>         needsBlock (Let _ _) = True
>         needsBlock (Switch _ _ _) = False
>         needsBlock (Choices _) = False
> ppStmt (Let bds st) =
>   ppSeq (ppKW "let" <+> ppBindings (map ppBinding bds)) st
>   where ppBinding (Bind v n) = ppName v <+> equals <+> ppExpr n
> ppStmt (Switch rf v cases) =
>   ppBlock (ppKW "switch" <+> ppName v <+> ppRF rf) (ppAlts ppCase cases)
>   where ppRF Rigid = ppKW "rigid"
>         ppRF Flex = ppKW "flex"
> ppStmt (Choices alts) = ppBlock (ppKW "choices") (ppAlts ppAlt alts)

> ppSeq :: Doc -> Stmt -> Doc
> ppSeq st1 st2 = st1 <> semi $$ ppStmt st2

> ppBindings :: [Doc] -> Doc
> ppBindings bds = lbrace <+> vcat (punctuate semi bds) <+> rbrace

> ppLiteral :: Literal -> Doc
> ppLiteral (Char c) = ppKW "char" <+> int (ord c)
> ppLiteral (Int i) = ppKW "int" <+> int i
> ppLiteral (Float f) = ppKW "float" <+> double f

> ppExpr :: Expr -> Doc
> ppExpr (Lit c) = ppLiteral c
> ppExpr (Constr c vs) = ppKW "data" <+> ppName c <> ppNames vs
> ppExpr (Closure f vs) = ppKW "function" <+> ppName f <> ppNames vs
> ppExpr (Lazy f vs) = ppKW "lazy" <+> ppName f <> ppNames vs
> ppExpr Free = ppKW "free"
> ppExpr (Ref v) = ppName v

> ppAlts :: (a -> Doc) -> [a] -> Doc
> ppAlts ppAlt = vcat . zipWith (<+>) (space : repeat bar) . map ppAlt

> ppCase :: Case -> Doc
> ppCase (Case t is) = ppCode (ppTag t <> colon) is
>   where ppTag (LitCase c) = ppLiteral c
>         ppTag (ConstrCase c vs) = ppKW "data" <+> ppName c <> ppNames vs
>         ppTag DefaultCase = ppKW "default"

> ppAlt :: Stmt -> Doc
> ppAlt = ppCode empty

> ppKW :: String -> Doc
> ppKW kw = char '.' <> text kw

> ppName :: Name -> Doc
> ppName = text . show

> ppNames :: [Name] -> Doc
> ppNames = parens . fsep . punctuate comma . map ppName

> bar :: Doc
> bar = char '|'

\end{verbatim}
