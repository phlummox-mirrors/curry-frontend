% $Id: ILxml.lhs,v 1.0 2001/06/19 12:19:18 rafa Exp $
%
% $Log: ILxml.lhs,v $
%
% Revision 1.1  2001/06/19 12:19:18  rafa
% Pretty printer in XML for the intermediate language added.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{ILxml.lhs}
\section{A pretty printer in XML for the intermediate language}
This module implements just another pretty printer, this time in XML and for
the intermediate language. It was mainly adapted from the Curry pretty
printer (see sect.~\ref{sec:CurryPP}), which in turn is based on Simon
Marlow's pretty printer for Haskell. The format of the output intends to be
similar to that of Flat-Curry XML representation.
\begin{verbatim}

> module Curry.IL.XML (xmlModule) where

> import Data.Maybe
> import Text.PrettyPrint.HughesPJ

> import Curry.Base.Ident
> import Curry.IL.Type

TODO: The following two imports should be avoided if possible as they make
  the program structure less clear.

> import qualified Curry.Syntax as CS
> import Env.CurryEnv

> -- identation level
> level::Int
> level = 3

> xmlModule :: CurryEnv -> Module -> Doc
> xmlModule cEnv m
>   = text "<prog>" $$ nest level (xmlBody cEnv m) $$ text "</prog>"

> xmlBody :: CurryEnv -> Module -> Doc
> xmlBody cEnv (Module mname mimports decls) =
>   xmlElement "module"      xmlModuleDecl      moduleDecl   $$
>   xmlElement "import"      xmlImportDecl      importDecl   $$
>   xmlElement "types"       xmlTypeDecl        typeDecl     $$
>   xmlElement "functions"   xmlFunctionDecl    functionDecl $$
>   xmlElement "operators"   xmlOperatorDecl    operatorDecl $$
>   xmlElement "translation" xmlTranslationDecl translationDecl
>   where
>     moduleDecl      = [mname]
>     importDecl      = mimports
>     operatorDecl    = infixDecls cEnv
>     translationDecl = foldl (qualIDeclId (moduleId cEnv)) [] (interface cEnv)
>     (functionDecl,typeDecl) = splitDecls decls

> xmlModuleDecl :: ModuleIdent -> Doc
> xmlModuleDecl = xmlModuleIdent

> xmlImportDecl :: ModuleIdent -> Doc
> xmlImportDecl mname = xmlElement "module" xmlModuleDecl  [mname]

=========================================================================
           T Y P E S
=========================================================================

> xmlTypeDecl :: Decl -> Doc
> xmlTypeDecl (DataDecl tc arity cs) =
>   beginType                                  $$
>   nest level (xmlTypeParams arity)           $$
>   xmlLines xmlConstructor cs                 $$
>   endType
>  where
>   beginType = text "<type name=\"" <> (xmlQualIdent tc) <> text "\">"
>   endType   = text "</type>"
> xmlTypeDecl _ = error "IL.XML.xmlTypeDecl: no data declaration"

> xmlTypeParams :: Int -> Doc
> xmlTypeParams n = xmlElement "params" xmlTypeVar [0..(n-1)]

> xmlConstructor :: ConstrDecl [Type] -> Doc
> xmlConstructor (ConstrDecl ident []) = xmlConstructorBegin ident 0
> xmlConstructor (ConstrDecl ident l)  =
>   xmlConstructorBegin ident (length l) $$
>   xmlLines xmlType l $$
>   xmlConstructorEnd
>  where
>   xmlConstructorEnd = text "</cons>"

> xmlConstructorBegin :: QualIdent -> Int -> Doc
> xmlConstructorBegin ident n = xmlHeadingWithArity "cons" ident n (n==0)

> xmlHeadingWithArity :: String -> QualIdent -> Int -> Bool -> Doc
> xmlHeadingWithArity tagName ident n single =
>   if single
>   then prefix<>text "/>"
>   else prefix<> text ">"
>   where
>     prefix = text ("<"++tagName++" name=\"") <> qname <> text "\" " <> arity
>     arity  = text "arity=\"" <> xmlInt n <> text "\""
>     qname  = xmlQualIdent ident

> xmlType :: Type -> Doc
> xmlType (TypeConstructor ident []) = xmlTypeConsBegin ident True
> xmlType (TypeConstructor ident l)  = xmlTypeConsBegin ident False $$
>                                      xmlLines xmlType l           $$
>                                      xmlTypeConsEnd
>                                      where
>                                        xmlTypeConsEnd = text "</tcons>"

> xmlType (TypeVariable n) = xmlTypeVar n
> xmlType (TypeArrow  a b) = xmlTypeFun a b

> xmlTypeConsBegin :: QualIdent -> Bool -> Doc
> xmlTypeConsBegin ident single =
>   if single
>   then prefix <> text "/>"
>   else prefix <> text ">"
>   where
>     qname  = xmlQualIdent ident
>     prefix = text "<tcons name=\"" <> qname <> text "\""

> xmlTypeVar :: Int -> Doc
> xmlTypeVar n = text "<tvar>"<> xmlInt n <> text "</tvar>"

> xmlTypeFun :: Type -> Type -> Doc
> xmlTypeFun a b =  xmlElement "functype" xmlType  [a,b]

=========================================================================
           F U N C T I O N S
=========================================================================

> xmlFunctionDecl :: Decl -> Doc
> xmlFunctionDecl (NewtypeDecl tc arity (ConstrDecl ident ty)) =
>   xmlFunctionDecl (FunctionDecl ident [arg] ftype (Variable arg))
>   where
>    arg = mkIdent "_1"
>    ftype = TypeArrow ty (TypeConstructor tc (map TypeVariable [0..arity-1]))

> xmlFunctionDecl (FunctionDecl ident largs fType expr) =
>    heading $$ nest level (xmlRule largs expr) $$ xmlEndFunction
>  where
>    heading = xmlBeginFunction ident (length largs) fType

> xmlFunctionDecl (ExternalDecl ident _callConv internalName fType) =
>    heading $$ external $$ xmlEndFunction
>  where
>    heading  = xmlBeginFunction ident (xmlFunctionArity fType) fType
>    external = text ("<external>"
>                     ++ xmlFormat internalName
>                     ++ "</external>")

> xmlFunctionDecl (DataDecl _ _ _) = error "IL.XML.xmlFunctionDecl: data declaration"

> xmlBeginFunction :: QualIdent -> Int -> Type -> Doc
> xmlBeginFunction ident n fType = heading $$ typeDecls
>    where
>      heading   = xmlHeadingWithArity "func" ident n False
>      typeDecls = nest level (xmlType fType)

> xmlEndFunction ::  Doc
> xmlEndFunction  = text "</func>"

> xmlFunctionArity :: Type -> Int
> xmlFunctionArity (TypeConstructor _ _) = 0
> xmlFunctionArity (TypeVariable _)      = 0
> xmlFunctionArity (TypeArrow _ b)       = 1 + (xmlFunctionArity b)

> xmlRule :: [Ident] -> Expression -> Doc
> xmlRule lArgs e = text "<rule>"               $$
>                   nest level (xmlLhs lArgs)   $$
>                   nest level (xmlRhs lArgs e) $$
>                   text "</rule>"

> xmlLhs :: [Ident] -> Doc
> xmlLhs l  = xmlElement "lhs" xmlVar [0..((length l)-1)]

> xmlRhs :: [Ident] -> Expression -> Doc
> xmlRhs l e = text "<rhs>"  $$ nest level rhs $$ text "</rhs>"
>              where
>                varDicc    = xmlBuildDicc l
>                (rhs, _) = xmlExpr varDicc e

=========================================================================
           E X P R E S S I O N S
=========================================================================

> xmlExpr :: [(Int,Ident)] -> Expression -> (Doc,[(Int,Ident)])
> xmlExpr d (Literal lit)  = (xmlLiteral (xmlLit lit),d)
> xmlExpr d (Variable ident)  = xmlExprVar d ident
> xmlExpr d (Function ident arity)    = (xmlSingleApp ident arity True,d)
> xmlExpr d (Constructor ident arity) = (xmlSingleApp ident arity False,d)
> xmlExpr d expr@(Apply _ _)          = xmlApply  d expr (xmlAppArgs expr)
> xmlExpr d (Case _ eval expr alt)      = xmlCase   d eval expr alt
> xmlExpr d (Or expr1 expr2)          = xmlOr     d expr1 expr2
> xmlExpr d (Exist ident expr)        = xmlFree   d ident expr
> xmlExpr d (Let binding expr)        = xmlLet    d binding expr
> xmlExpr d (Letrec lBinding expr)    = xmlLetrec d lBinding expr
>   --error "Recursive let bindings not supported in FlatCurry"

> xmlSingleApp :: QualIdent -> Int -> Bool -> Doc
> xmlSingleApp ident arity isFunction =
>    if arity>0
>    then xmlCombHeading identDoc (text "PartCall") True
>    else xmlCombHeading identDoc (text totalApp) True
>    where
>       identDoc = xmlQualIdent ident
>       totalApp = if isFunction then "FuncCall" else "ConsCall"

> xmlCombHeading :: Doc -> Doc -> Bool -> Doc
> xmlCombHeading cname cType single =
>     if single
>     then prefix <> text " />"
>     else prefix <> text ">"
>     where
>       prefix = text "<comb type=\""<>cType<>text "\" name=\""<>cname<>text "\""

> xmlExprVar :: [(Int,Ident)] -> Ident -> (Doc,[(Int,Ident)])
> xmlExprVar d ident =
>    if isNew
>    then (xmlVar newVar, (newVar,ident):d)
>    else (xmlVar var, d)
>    where
>       var    = xmlLookUp ident d
>       isNew  = var == -1
>       newVar = xmlNewVar d

> xmlApply :: [(Int,Ident)] -> Expression -> (Expression,[Expression]) ->
>              (Doc,[(Int,Ident)])
> xmlApply d _ ((Function ident arity),lExp) =
>   xmlApplyFunctor d ident arity lExp True
> xmlApply d _ ((Constructor ident arity),lExp) =
>   xmlApplyFunctor d ident arity lExp False
> xmlApply d (Apply expr1 expr2) _ =
>   (text "<apply>" $$ nest level e1 $$ nest level e2 $$ text "</apply>", d2)
>     where
>        (e1,d1) = xmlExpr d  expr1
>        (e2,d2) = xmlExpr d1 expr2
> xmlApply _ _ _ = error "IL.XML.xmlApply: no pattern match"

> xmlApplyFunctor ::[(Int,Ident)] -> QualIdent -> Int -> [Expression] ->
>                     Bool -> (Doc,[(Int,Ident)])
> xmlApplyFunctor d ident arity lArgs isFunction =
>    xmlCombApply d (xmlQualIdent ident)  (text cTypeS) n lArgs
>    where
>       n     = length (lArgs)
>       cTypeS = if n==arity
>               then if isFunction
>                    then "FuncCall"
>                    else "ConsCall"
>               else "PartCall"

> xmlCombApply :: [(Int,Ident)] -> Doc -> Doc -> Int ->
>                                 [Expression] -> (Doc,[(Int,Ident)])
> xmlCombApply d cname cType 0 _ =
>    (xmlCombHeading cname cType True,d)
> xmlCombApply d cname cType _ lArgs =
>    (xmlCombHeading cname cType False $$ xmlLines id lDocs$$ text "</comb>", d1)
>    where
>      (lDocs,d1) = xmlMapDicc d xmlExpr lArgs

> xmlAppArgs :: Expression -> (Expression,[Expression])
> xmlAppArgs (Apply e1 e2) = (e,lArgs++[e2])
>                            where
>                                (e,lArgs) = (xmlAppArgs e1)
> xmlAppArgs e             = (e,[])

> xmlCase :: [(Int,Ident)] -> Eval -> Expression -> [Alt] -> (Doc,[(Int,Ident)])
> xmlCase d eval expr lAlt =
>   (heading $$ nest level e1 $$ xmlLines id lDocs$$ end,d2)
>   where
>     sEval      = if eval==Rigid then "\"Rigid\"" else "\"Flex\""
>     heading    = text "<case type=" <> text sEval <> text ">"
>     end        = text "</case>"
>     (e1,_)    = xmlExpr d expr
>     (lDocs,d2) = xmlMapDicc d xmlBranch  lAlt

> xmlOr :: [(Int,Ident)] -> Expression -> Expression -> (Doc,[(Int,Ident)])
> xmlOr d  expr1 expr2 =
>    (text "<or>" $$ nest level e1 $$ nest level e2 $$  text "</or>",d2)
>    where
>      (e1,d1) = xmlExpr d expr1
>      (e2,d2) = xmlExpr d1 expr2

> xmlBranch :: [(Int,Ident)] -> Alt -> (Doc,[(Int,Ident)])
> xmlBranch d (Alt pattern expr) =
>    (text "<branch>" $$ nest level e1 $$ nest level e2 $$ text "</branch>",d2)
>    where
>      (e1,d1) = xmlPattern d pattern
>      (e2,d2) = xmlExpr d1 expr

> xmlPattern :: [(Int,Ident)] -> ConstrTerm -> (Doc,[(Int,Ident)])
> xmlPattern d (LiteralPattern lit) = (xmlLitPattern (xmlLit lit),d)
> xmlPattern d (ConstructorPattern ident lArgs) = xmlConsPattern d ident  lArgs
> xmlPattern _ (VariablePattern _) = error "Variable patterns not allowed in Flat Curry"

> xmlConsPattern :: [(Int,Ident)] -> QualIdent -> [Ident] -> (Doc,[(Int,Ident)])
> xmlConsPattern d ident lArgs =
>    (heading $$ xmlLines id lDocs $$ end,d2)
>    where
>      heading    = text "<pattern name=\""<> (xmlQualIdent ident) <>
>                   text "\"" <> endh
>      endh       = if (length lArgs)>0 then text ">" else text "/>"
>      end        = if (length lArgs)>0 then text "</pattern>" else empty
>      (lDocs,d2) = xmlMapDicc d xmlExprVar lArgs

> xmlFree :: [(Int,Ident)] -> Ident -> Expression -> (Doc,[(Int,Ident)])
> xmlFree d ident expr =
>  (text "<freevars>" $$ nest level v $$ nest level e $$ text "</freevars>",d2)
>                    where
>                       (v,d1) = xmlExprVar d  ident
>                       (e,d2) = xmlExpr d1 expr

> xmlLet :: [(Int,Ident)] -> Binding -> Expression -> (Doc,[(Int,Ident)])
> xmlLet d binding expr =
>   (text "<let>" $$ nest level b $$ nest level e $$ text "</let>", d2)
>   where
>    (b,d1) = xmlBinding d binding
>    (e,d2) = xmlExpr d1 expr

> xmlBinding :: [(Int,Ident)] -> Binding -> (Doc,[(Int,Ident)])
> xmlBinding d  (Binding ident expr) =
>    (text "<binding>" $$ nest level v $$ nest level e $$ text "</binding>",d2)
>    where
>       (v,_)  = xmlExprVar d ident
>       (e,d2) = xmlExpr d expr

> xmlLetrec :: [(Int,Ident)] -> [Binding] -> Expression -> (Doc,[(Int,Ident)])
> xmlLetrec d lB expr =
>   (text "<letrec>" $$ xmlLines id b $$ nest level e $$ text "</letrec>",d2)
>   where
>     (b,d1) = xmlMapDicc d xmlBinding lB
>     (e,d2) = xmlExpr d1 expr

=========================================================================
            A U X I L I A R Y  F U N C T I O N S
=========================================================================

> splitDecls :: [Decl] -> ([Decl],[Decl])
> splitDecls []     = ([],[])
> splitDecls (x:xs) = case x of
>                      DataDecl     _ _ _   -> (functionDecl,x:typeDecl)
>                      NewtypeDecl  _ _ _   -> (x:functionDecl,typeDecl)
>                      FunctionDecl _ _ _ _ -> (x:functionDecl,typeDecl)
>                      ExternalDecl _ _ _ _   -> (x:functionDecl,typeDecl)
>                   where
>                       (functionDecl,typeDecl) = splitDecls xs

> xmlElement :: Eq a => String -> (a -> Doc) -> [a] -> Doc
> xmlElement n _ []     = text ("<" ++ n ++ " />")
> xmlElement n f lDecls = beginElement $$ xmlLines f lDecls $$ endElement
>                            where
>                                beginElement = text ("<"++n++">")
>                                endElement   = text ("</"++n++">")
>

> xmlLines :: (a -> Doc) -> [a] -> Doc
> xmlLines f = (nest level).vcat.(map f)

> xmlMapDicc::[(Int,Ident)] -> ([(Int,Ident)] -> a -> (Doc,[(Int,Ident)])) ->
>              [a] -> ([Doc],[(Int,Ident)])
> xmlMapDicc d f lArgs = foldl newArg ([],d) lArgs
>                             where
>                               newArg (l,d')  e = (l++[v'],d'')
>                                                 where (v',d'') = f d' e
>

> -- The dictionary identifies var names with integers
> -- it will be ordered starting at the greatest integer
> xmlBuildDicc :: [Ident] -> [(Int,Ident)]
> xmlBuildDicc l = reverse (zip [0..((length l)-1)] l)

> -- looks for a ident in the dictorionary. If it appears returns its
> -- associated value. Otherwise, -1 is returned
> xmlLookUp :: Ident -> [(Int,Ident)] -> Int
> xmlLookUp _       []          = -1
> xmlLookUp ident ((n,idName):xs) = if ident==idName
>                                 then n
>                                 else xmlLookUp ident xs

> -- generates a integer corresponding to a new var
> xmlNewVar :: [(Int, Ident)] -> Int
> xmlNewVar []        = 0
> xmlNewVar ((n,_):_) = n+1

> xmlVar :: Int -> Doc
> xmlVar n = text "<var>" <> xmlInt n <> text "</var>"

> xmlLiteral :: Doc -> Doc
> xmlLiteral d =   text "<lit>" $$ nest level d $$ text "</lit>"

> xmlLitPattern :: Doc -> Doc
> xmlLitPattern d =   text "<lpattern>" $$ nest level d $$ text "</lpattern>"

> xmlLit :: Literal -> Doc
> xmlLit (Char _ c) = text "<charc>" <>  xmlInt (fromEnum c) <> text "</charc>"
> xmlLit (Int _ n) = text "<intc>" <>  xmlInteger n <> text "</intc>"
> xmlLit (Float _ n) = text "<floatc>" <>  xmlFloat n <> text "</floatc>"

> xmlOperatorDecl :: CS.IDecl -> Doc
> xmlOperatorDecl (CS.IInfixDecl _ fixity prec qident) =
>     text "<op fixity=\"" <> xmlFixity fixity
>     <> text "\" prec=\"" <> xmlInteger prec <> text "\">"
>     <> xmlIdent (unqualify qident)
>     <> text "</op>"
> xmlOperatorDecl _ = error "IL.XML.xmlOperatorDecl: no pattern match"

> xmlFixity :: CS.Infix -> Doc
> xmlFixity CS.InfixL = text "InfixlOp"
> xmlFixity CS.InfixR = text "InfixrOp"
> xmlFixity CS.Infix  = text "InfixOp"

> xmlTranslationDecl :: QualIdent -> Doc
> xmlTranslationDecl expId =
>       text "<trans>"
>    $$ nest level (   text "<name>"    <> xmlIdent (unqualify expId) <> text "</name>"
>                   $$ text "<intname>" <> xmlQualIdent expId         <> text "</intname>")
>    $$ text "</trans>"

> xmlIdent :: Ident -> Doc
> xmlIdent ident = text (xmlFormat (name ident))

> xmlInt :: Int -> Doc
> xmlInt n = text (show n)

> xmlInteger :: Integer -> Doc
> xmlInteger n = text (show n)

> xmlFloat :: Double -> Doc
> xmlFloat n = text (show n)

> xmlQualIdent :: QualIdent -> Doc
> xmlQualIdent ident = text (xmlFormat (qualName ident))

> xmlModuleIdent:: ModuleIdent -> Doc
> xmlModuleIdent n = text (xmlFormat (moduleName n))

> xmlFormat :: String -> String
> xmlFormat []       = []
> xmlFormat ('>':xs) = "&gt;"++xmlFormat xs
> xmlFormat ('<':xs) = "&lt;"++xmlFormat xs
> xmlFormat ('&':xs) = "&amp;"++xmlFormat xs
> xmlFormat (x:xs)   = x:(xmlFormat xs)

> qualIDeclId :: ModuleIdent -> [QualIdent] -> CS.IDecl -> [QualIdent]
> qualIDeclId mid qids (CS.IDataDecl _ qid _ mcdecls)
>    = foldl (qualConstrDeclId mid) (qid:qids) (catMaybes mcdecls)
> qualIDeclId mid qids (CS.INewtypeDecl _ qid _ ncdecl)
>    = qualNewConstrDeclId mid (qid:qids) ncdecl
> qualIDeclId _ qids (CS.ITypeDecl _ qid _ _)
>    = qid:qids
> qualIDeclId _ qids (CS.IFunctionDecl _ qid _ _)
>    = qid:qids
> qualIDeclId _ qids _ = qids

> qualConstrDeclId :: ModuleIdent -> [QualIdent] -> CS.ConstrDecl -> [QualIdent]
> qualConstrDeclId mid qids (CS.ConstrDecl _ _ ident _)
>    = (qualifyWith mid ident):qids
> qualConstrDeclId mid qids (CS.ConOpDecl _ _ _ ident _)
>    = (qualifyWith mid ident):qids

> qualNewConstrDeclId :: ModuleIdent -> [QualIdent] -> CS.NewConstrDecl
>	                 -> [QualIdent]
> qualNewConstrDeclId mid qids (CS.NewConstrDecl _ _ ident _)
>    = (qualifyWith mid ident):qids

\end{verbatim}
