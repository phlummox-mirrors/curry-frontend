module CurryInfo (CurryInfo, genCurryInfo,
                  getExports, getOpFixity, getTypeSyns) where

import CurrySyntax
import Ident
import Maybe

------------------------------------------------------------------------------

data CurryInfo = CurryInfo { exports  :: [Ident],
			     ops      :: [IDecl],
			     typesyns :: [IDecl]
			   }

-------------------------------------------------------------------------------

--
genCurryInfo :: Module -> CurryInfo
genCurryInfo mod = CurryInfo expinfo opinfo tsyninfo
 where
 expinfo  = genExportInfo mod
 opinfo   = genOpInfo mod
 tsyninfo = genTypeSynInfo mod


--
getExports :: CurryInfo -> [Ident]
getExports info = exports info

--
getOpFixity :: CurryInfo -> [IDecl]
getOpFixity info = ops info

--
getTypeSyns :: CurryInfo -> [IDecl]
getTypeSyns info = typesyns info


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
genExportInfo :: Module -> [Ident]
genExportInfo (Module mident expspec decls)
   | isJust expspec = getPublicIdsFromExports mident (fromJust expspec) decls
   | otherwise      = getIdentsFromTopLevelDecls decls


--
getPublicIdsFromExports ::  ModuleIdent -> ExportSpec -> [Decl] -> [Ident]
getPublicIdsFromExports mident (Exporting pos exps) decls =
   getIdentsFromExports mident decls (map name (getIdentsFromTopLevelDecls decls)) exps 


--
getIdentsFromExports :: ModuleIdent -> [Decl] -> [String] -> [Export] -> [Ident]
getIdentsFromExports mident decls names [] = []

getIdentsFromExports mident decls names ((Export qident):es)
   | isDeclaredIdent qident mident names
     = (unqualify qident):(getIdentsFromExports mident decls names es)
   | otherwise
     = getIdentsFromExports mident decls names es

getIdentsFromExports mident decls names ((ExportTypeWith qident cidents):es)
   | isDeclaredIdent qident mident names
     = cidents ++ ((unqualify qident):(getIdentsFromExports mident decls names es))
   | otherwise
     = getIdentsFromExports mident decls names es

getIdentsFromExports mident decls names ((ExportTypeAll qident):es) =
   getIdentsFromExports  mident
                         decls 
                         names
                         ((ExportTypeWith qident 
                                          (getConstrIdentsForDataType (unqualify qident) decls)):es)

getIdentsFromExports mident decls names ((ExportModule mident'):es) =
   getIdentsFromExports mident decls names es


--
isDeclaredIdent :: QualIdent -> ModuleIdent -> [String] -> Bool
isDeclaredIdent qident mident names 
   = isJust (localIdent mident qident) && any ((==) (name (unqualify qident))) names


--
getConstrIdentsForDataType :: Ident -> [Decl] -> [Ident]
getConstrIdentsForDataType ident [] = []
getConstrIdentsForDataType ident (decl:decls) =
   case decl of
     (DataDecl pos tident args cdecls) 
	     -> if (name ident) == (name tident)
		   then map p_getConstrIdent cdecls
                   else getConstrIdentsForDataType ident decls
     _       -> getConstrIdentsForDataType ident decls
 where
   p_getConstrIdent (ConstrDecl pos ids cident texpr)      = cident
   p_getConstrIdent (ConOpDecl pos ids ltype cident rtype) = cident


--
getIdentsFromTopLevelDecls :: [Decl] -> [Ident]
getIdentsFromTopLevelDecls [] = []
getIdentsFromTopLevelDecls ((ImportDecl pos mident' qual mids specs):decls) =
   getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((InfixDecl pos fix prec idents):decls) =
   getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((DataDecl pos ident args cdecls):decls) =
   ident:(map getIdentFromConstrDecl cdecls) ++ getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((NewtypeDecl pos ident args ncdecl):decls) =
   (getIdentFromNewConstrDecl ncdecl):(getIdentsFromTopLevelDecls decls)
getIdentsFromTopLevelDecls ((TypeDecl pos ident args texpr):decls) =
   ident:(getIdentsFromTopLevelDecls decls)
getIdentsFromTopLevelDecls ((TypeSig pos idents texpr):decls) =
   getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((EvalAnnot pos idents annot):decls) =
   getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((FunctionDecl pos ident equs):decls) =
   ident:(getIdentsFromTopLevelDecls decls)
getIdentsFromTopLevelDecls ((ExternalDecl pos conv name ident texpr):decls) =
   ident:(getIdentsFromTopLevelDecls decls)
getIdentsFromTopLevelDecls ((FlatExternalDecl pos idents):decls) =
   getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((PatternDecl pos cterm rhs):decls) =
   getIdentsFromTopLevelDecls decls
getIdentsFromTopLevelDecls ((ExtraVariables pos idents):decls) =
   getIdentsFromTopLevelDecls decls


--
getIdentFromConstrDecl :: ConstrDecl -> Ident
getIdentFromConstrDecl (ConstrDecl pos ids ident texpr)      = ident
getIdentFromConstrDecl (ConOpDecl pos ids ltype ident rtype) = ident


getIdentFromNewConstrDecl ::  NewConstrDecl -> Ident
getIdentFromNewConstrDecl (NewConstrDecl pos ids ident texpr) = ident


-------------------------------------------------------------------------------

--
genOpInfo :: Module -> [IDecl]
genOpInfo (Module mident expspec decls)
   = collectIInfixDecls mident decls

--
collectIInfixDecls :: ModuleIdent -> [Decl] -> [IDecl]
collectIInfixDecls mident [] = []
collectIInfixDecls mident ((InfixDecl pos infixspec prec idents):decls)
   = (map (\ident 
	   -> IInfixDecl pos infixspec prec (qualifyWith mident ident)) 
	   idents)
     ++ (collectIInfixDecls mident decls)
collectIInfixDecls mident (_:decls) = collectIInfixDecls mident decls


-------------------------------------------------------------------------------

--
genTypeSynInfo :: Module -> [IDecl]
genTypeSynInfo (Module mident expspec decls)
   = collectITypeDecls mident decls


--
collectITypeDecls :: ModuleIdent -> [Decl] -> [IDecl]
collectITypeDecls mident [] = []
collectITypeDecls mident ((TypeDecl pos ident params typeexpr):decls)
   = (ITypeDecl pos (qualifyWith mident ident) params 
                (simplifyTypeExpr typeexpr))
     :(collectITypeDecls mident decls)
collectITypeDecls mident (_:decls) = collectITypeDecls mident decls


--
simplifyTypeExpr :: TypeExpr -> TypeExpr
simplifyTypeExpr (ConstructorType qident typeexprs)
   = (ConstructorType qident (map simplifyTypeExpr typeexprs))
simplifyTypeExpr (VariableType ident)
   = (VariableType ident)
simplifyTypeExpr (ArrowType type1 type2)
   = (ArrowType (simplifyTypeExpr type1) (simplifyTypeExpr type2))
simplifyTypeExpr (TupleType typeexprs)
   = (ConstructorType (qTupleId (length typeexprs)) 
                      (map simplifyTypeExpr typeexprs))
simplifyTypeExpr (ListType typeexpr)
   = (ConstructorType (qualify listId) [(simplifyTypeExpr typeexpr)])


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


