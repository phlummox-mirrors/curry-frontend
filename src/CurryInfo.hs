module CurryInfo (CurryInfo, genCurryInfo,
		  getModuleName, getPublicIds,
                  getExports, getOpFixity, getTypeSyns) where

import CurrySyntax
import Ident
import Base
import Env
import Maybe

------------------------------------------------------------------------------

data CurryInfo = CurryInfo { modname  :: ModuleIdent,
			     exports  :: [Export],
			     publics  :: [QualIdent],
			     ops      :: [IDecl],
			     typesyns :: [IDecl]
			   }

-------------------------------------------------------------------------------

--
genCurryInfo :: ModuleEnv -> Module -> CurryInfo
genCurryInfo menv mod = CurryInfo { modname  = genModuleName menv mod,
				    exports  = genExports menv mod,
				    publics  = genExportInfo menv mod,
				    ops      = genOpInfo menv mod,
				    typesyns = genTypeSynInfo menv mod
				  }

--
getModuleName :: CurryInfo -> ModuleIdent
getModuleName info = modname info

--
getExports :: CurryInfo -> [Export]
getExports info = exports info

--
getPublicIds :: CurryInfo -> [QualIdent]
getPublicIds info = publics info

--
getOpFixity :: CurryInfo -> [IDecl]
getOpFixity info = ops info

--
getTypeSyns :: CurryInfo -> [IDecl]
getTypeSyns info = typesyns info


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
genModuleName :: ModuleEnv -> Module -> ModuleIdent
genModuleName _ (Module mident _ _) = mident


-------------------------------------------------------------------------------

--
genExports :: ModuleEnv -> Module -> [Export]
genExports menv (Module mident (Just (Exporting pos exps)) decls) 
   = filter (isExportedImport mident) exps
genExports menv _
   = []


--
isExportedImport :: ModuleIdent -> Export -> Bool
isExportedImport mident (Export qident) 
   = isNothing (localIdent mident qident)
isExportedImport mident (ExportTypeWith qident _)
   = isNothing (localIdent mident qident)
isExportedImport mident (ExportTypeAll qident)
   = isNothing (localIdent mident qident)
isExportedImport mident (ExportModule mident')
   = mident /= mident'


-------------------------------------------------------------------------------

--
genExportInfo :: ModuleEnv -> Module -> [QualIdent]
genExportInfo menv (Module mident expspec decls)
   | isJust expspec = getPublicIdsFromExports menv mident (fromJust expspec) decls
   | otherwise      = map (qualifyWith mident) (getIdentsFromTopLevelDecls decls)


--
getPublicIdsFromExports :: ModuleEnv ->  ModuleIdent -> ExportSpec -> [Decl] 
			-> [QualIdent]
getPublicIdsFromExports menv mident (Exporting pos exps) decls
   = getIdentsFromExports menv 
		       	  mident 
			  decls 
			  exps 


--
getIdentsFromExports :: ModuleEnv -> ModuleIdent -> [Decl] -> [Export] 
		     -> [QualIdent]
getIdentsFromExports menv mident decls [] = []

getIdentsFromExports menv mident decls ((Export qident):es)
   = qident:(getIdentsFromExports menv mident decls es)

getIdentsFromExports menv mident decls ((ExportTypeWith qident cidents):es)
   = (map (qualifyWith mident) cidents) 
     ++ qident:(getIdentsFromExports menv mident decls es)

getIdentsFromExports menv mident decls ((ExportTypeAll qident):es)
   = getIdentsFromExports 
       menv
       mident 
       decls 
       ((ExportTypeWith qident 
	 (getConstrIdentsForDataType (unqualify qident) decls)):es)

getIdentsFromExports menv mident decls ((ExportModule mident'):es)
   = map (qualifyWith mident') 
         (maybe [] getIdentsFromIDecls (lookupEnv mident' menv))
     ++ (getIdentsFromExports menv mident decls es)


--
--isDeclaredIdent :: QualIdent -> ModuleIdent -> [String] -> Bool
--isDeclaredIdent qident mident names 
--   = isJust (localIdent mident qident) && any ((==) (name (unqualify qident))) names


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

--
getIdentFromNewConstrDecl ::  NewConstrDecl -> Ident
getIdentFromNewConstrDecl (NewConstrDecl pos ids ident texpr) = ident


--
getIdentsFromIDecls :: [IDecl] -> [Ident]
getIdentsFromIDecls [] = []
getIdentsFromIDecls ((IImportDecl _ _):idecls)
   = getIdentsFromIDecls idecls
getIdentsFromIDecls ((IInfixDecl _ _ _ _):idecls)
   = getIdentsFromIDecls idecls
getIdentsFromIDecls ((HidingDataDecl _ _ _):idecls)
   = getIdentsFromIDecls idecls
getIdentsFromIDecls ((IDataDecl _ qident _ mcdecls):idecls)
   = (map (getIdentFromConstrDecl . fromJust) (filter isJust mcdecls))
     ++ (unqualify qident):(getIdentsFromIDecls idecls)
getIdentsFromIDecls ((INewtypeDecl _ qident _ ncdecl):idecls)
   = (getIdentFromNewConstrDecl ncdecl):(getIdentsFromIDecls idecls)
getIdentsFromIDecls ((ITypeDecl _ qident _ _):idecls)
   = (unqualify qident):(getIdentsFromIDecls idecls)
getIdentsFromIDecls ((IFunctionDecl _ qident _):idecls)
   = (unqualify qident):(getIdentsFromIDecls idecls)


-------------------------------------------------------------------------------

--
genOpInfo :: ModuleEnv -> Module -> [IDecl]
genOpInfo _ (Module mident expspec decls)
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
genTypeSynInfo :: ModuleEnv -> Module -> [IDecl]
genTypeSynInfo _ (Module mident expspec decls)
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


