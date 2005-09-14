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
genCurryInfo :: ModuleEnv -> TCEnv -> Module -> CurryInfo
genCurryInfo menv tcEnv mod 
   = CurryInfo { modname  = genModuleName menv mod,
		 exports  = genExports menv mod,
		 publics  = genExportInfo menv mod,
		 ops      = genOpInfo menv mod,
		 typesyns = genTypeSynInfo tcEnv mod
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
genTypeSynInfo :: TCEnv -> Module -> [IDecl]
genTypeSynInfo tcEnv (Module mident expspec decls)
   = map (genTypeSynDecl mident tcEnv) 
         [ident | ident@(TypeDecl _ _ _ _) <- decls]
--   = collectITypeDecls tcEnv mident decls

--
--genTypeSynDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
--genTypeSynDecl mident tcEnv qident
--   = maybe (internalError "missing definition for \"" ++ show qident ++ "\"")
--           (\typeexpr -> ITypeDecl (first (moduleName mident)) 
--	                           qident
--	                           BLA
--	                           typeexpr)

--
--collectITypeDecls :: TCEnv -> ModuleIdent -> [Decl] -> [IDecl]
--collectITypeDecls _ mident [] = []
--collectITypeDecls tcEnv mident ((TypeDecl pos ident params typeexpr):decls)
----   = ITypeDecl pos qident params 
----               (fromMaybe (simplifyTypeExpr typeexpr)
----		          (lookupAliasType qident tcEnv)
---- where qident = qualifyWith mident ident
--   = (ITypeDecl pos (qualifyWith mident ident) params 
--                (simplifyTypeExpr tcEnv typeexpr))
--     :(collectITypeDecls tcEnv mident decls)
--collectITypeDecls tcEnv mident (_:decls) 
--   = collectITypeDecls tcEnv mident decls

--
genTypeSynDecl :: ModuleIdent -> TCEnv -> Decl -> IDecl
genTypeSynDecl mid tcEnv (TypeDecl pos ident params typeexpr)
   = ITypeDecl pos (qualifyWith mid ident) params 
               (modifyTypeExpr tcEnv typeexpr)
genTypeSynDecl _ _ _ 
   = internalError "@CurryInfo.genTypeSynDecl: illegal declaration"


--
modifyTypeExpr :: TCEnv -> TypeExpr -> TypeExpr
modifyTypeExpr tcEnv (ConstructorType qident typeexprs)
   = case (qualLookupTC qident tcEnv) of
       [AliasType _ arity rhstype]
          -> modifyTypeExpr tcEnv 
	                    (genTypeSynDeref (zip [0 .. (arity-1)] typeexprs)
			                     rhstype)
       _  -> ConstructorType (fromMaybe qident (lookupTCId qident tcEnv))
                             (map (modifyTypeExpr tcEnv) typeexprs)
modifyTypeExpr _ (VariableType ident)
   = VariableType ident
modifyTypeExpr tcEnv (ArrowType type1 type2)
   = ArrowType (modifyTypeExpr tcEnv type1) (modifyTypeExpr tcEnv type2)
modifyTypeExpr tcEnv (TupleType typeexprs)
   | null typeexprs 
     = ConstructorType qUnitId []
   | otherwise
     = ConstructorType (qTupleId (length typeexprs)) 
                       (map (modifyTypeExpr tcEnv) typeexprs)
modifyTypeExpr tcEnv (ListType typeexpr)
   = (ConstructorType (qualify listId) [(modifyTypeExpr tcEnv typeexpr)])

--
genTypeSynDeref :: [(Int,TypeExpr)] -> Type -> TypeExpr
genTypeSynDeref its (TypeConstructor qident typeexprs)
   = ConstructorType qident (map (genTypeSynDeref its) typeexprs)
genTypeSynDeref its (TypeVariable i)
   = fromMaybe (internalError ("@CurryInfo.genTypeSynDeref: " ++
			       "unkown type var index"))
               (lookup i its)
genTypeSynDeref its (TypeConstrained typeexprs i)
   = internalError ("@CurryInfo.genTypeSynDeref: " ++
		    "illegal constrained type occured")
genTypeSynDeref its (TypeArrow type1 type2)
   = ArrowType (genTypeSynDeref its type1) (genTypeSynDeref its type2)
genTypeSynDeref its (TypeSkolem i)
   = internalError ("@CurryInfo.genTypeSynDeref: " ++
		    "illegal skolem type occured")

--
lookupTCId :: QualIdent -> TCEnv -> Maybe QualIdent
lookupTCId qident tcEnv
   = case (qualLookupTC qident tcEnv) of
       [DataType qident' _ _]     -> Just qident'
       [RenamingType qident' _ _] -> Just qident'
       [AliasType qident' _ _]    -> Just qident'
       _                          -> Nothing


-- Looks up the declaration of a type synonym
--lookupAliasType :: QualIdent -> TCEnv -> Maybe Type
--lookupAliasType qident tcEnv 
--   = case (qualLookupTC qident tcEnv) of
--       [AliasType _ _ t]    -> Just t
--       _                    -> Nothing

--
--convertType :: Type -> TypeExpr
--convertType (TypeConstructor qident typeexprs)
--   = ConstructorType qident (map convertType typeexprs)
--convertType (TypeVariable idx)
--   = VariableType (mkIdent ("a" ++ show idx))
--convertType (TypeConstrained typeexprs idx)
--   = internalError "constrained type occured in type synonym"
--convertType (TypeArrow type1 type2)
--   = ArrowType (convertType type1) (convertType type2)
--convertType (TypeSkolem idx)
--   = internalError "skolem type occured in type synonym"


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


