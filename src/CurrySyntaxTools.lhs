> module CurrySyntaxTools (getPublicIdents) where

> import CurrySyntax
> import Ident
> import Maybe

>------------------------------------------------------------------------------

> getPublicIdents :: Module -> [Ident]
> getPublicIdents (Module mident expspec decls)
>    | isJust expspec = getPublicIdsFromExports mident decls (fromJust expspec)
>    | otherwise      = getIdentsFromTopLevelDecls decls


> getOpInfixDecls :: Module -> [(Ident, (Infix, Int))]
> getOpInfixDecls (Module mident expspec decls) = collectOpInfixDecls decls


> isInfix :: Infix -> Bool
> isInfix Infix = True
> isInfix _     = False

> isInfixL :: Infix -> Bool
> isInfixL InfixL = True
> isInfixL _      = False

> isInfixR :: Infix -> Bool
> isInfixR InfixR = True
> isInfixR _      = False


------------------------------------------------------------------------------

> getPublicIdsFromExports ::  ModuleIdent -> [Decl] -> ExportSpec -> [Ident]
> getPublicIdsFromExports mident decls (Exporting pos exps) =
>    getIdentsFromExports mident decls (map name (getIdentsFromTopLevelDecls decls)) exps 


> getIdentsFromExports :: ModuleIdent -> [Decl] -> [String] -> [Export] -> [Ident]
> getIdentsFromExports mident decls names [] = []
> 
> getIdentsFromExports mident decls names ((Export qident):es)
>    | isDeclaredIdent qident mident names
>      = (unqualify qident):(getIdentsFromExports mident decls names es)
>    | otherwise
>      = getIdentsFromExports mident decls names es
> 
> getIdentsFromExports mident decls names ((ExportTypeWith qident cidents):es)
>    | isDeclaredIdent qident mident names
>      = cidents ++ ((unqualify qident):(getIdentsFromExports mident decls names es))
>    | otherwise
>      = getIdentsFromExports mident decls names es
> 
> getIdentsFromExports mident decls names ((ExportTypeAll qident):es) =
>    getIdentsFromExports  mident
>                          decls 
>                          names
>                          ((ExportTypeWith qident 
>                                           (getConstrIdentsForDataType (unqualify qident) decls)):es)
> 
> getIdentsFromExports mident decls names ((ExportModule mident'):es) =
>    getIdentsFromExports mident decls names es


> isDeclaredIdent :: QualIdent -> ModuleIdent -> [String] -> Bool
> isDeclaredIdent qident mident names 
>    = isJust (localIdent mident qident) && any ((==) (name (unqualify qident))) names


> getConstrIdentsForDataType :: Ident -> [Decl] -> [Ident]
> getConstrIdentsForDataType ident [] = []
> getConstrIdentsForDataType ident (decl:decls) =
>    case decl of
>      (DataDecl pos tident args cdecls) -> if (name ident) == (name tident)
>                                              then map p_getConstrIdent cdecls
>                                              else getConstrIdentsForDataType ident decls
>      _                                 -> getConstrIdentsForDataType ident decls
>  where
>    p_getConstrIdent (ConstrDecl pos ids cident texpr)      = cident
>    p_getConstrIdent (ConOpDecl pos ids ltype cident rtype) = cident



> getIdentsFromTopLevelDecls :: [Decl] -> [Ident]
> getIdentsFromTopLevelDecls [] = []
> getIdentsFromTopLevelDecls ((ImportDecl pos mident' qual mids specs):decls) =
>    getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((InfixDecl pos fix prec idents):decls) =
>    getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((DataDecl pos ident args cdecls):decls) =
>    ident:(map getIdentFromConstrDecl cdecls) ++ getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((NewtypeDecl pos ident args ncdecl):decls) =
>    (getIdentFromNewConstrDecl ncdecl):(getIdentsFromTopLevelDecls decls)
> getIdentsFromTopLevelDecls ((TypeDecl pos ident args texpr):decls) =
>    ident:(getIdentsFromTopLevelDecls decls)
> getIdentsFromTopLevelDecls ((TypeSig pos idents texpr):decls) =
>    getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((EvalAnnot pos idents annot):decls) =
>    getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((FunctionDecl pos ident equs):decls) =
>    ident:(getIdentsFromTopLevelDecls decls)
> getIdentsFromTopLevelDecls ((ExternalDecl pos conv name ident texpr):decls) =
>    ident:(getIdentsFromTopLevelDecls decls)
> getIdentsFromTopLevelDecls ((FlatExternalDecl pos idents):decls) =
>    getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((PatternDecl pos cterm rhs):decls) =
>    getIdentsFromTopLevelDecls decls
> getIdentsFromTopLevelDecls ((ExtraVariables pos idents):decls) =
>    getIdentsFromTopLevelDecls decls


> getIdentFromConstrDecl :: ConstrDecl -> Ident
> getIdentFromConstrDecl (ConstrDecl pos ids ident texpr)      = ident
> getIdentFromConstrDecl (ConOpDecl pos ids ltype ident rtype) = ident


> getIdentFromNewConstrDecl ::  NewConstrDecl -> Ident
> getIdentFromNewConstrDecl (NewConstrDecl pos ids ident texpr) = ident


-------------------------------------------------------------------------------

> collectOpInfixDecls :: [Decl] -> [(Ident, (Infix, Int))]
> collectOpInfixDecls [] = []
> collectOpInfixDecls ((InfixDecl _ infixspec prec idents):decls)
>    = (map (\ident -> (ident, (infixspec, fromInteger prec))) idents)
>      ++ (collectOpInfixDecls decls)
> collectOpInfixDecls (_:decls) = collectOpInfixDecls decls


-------------------------------------------------------------------------------