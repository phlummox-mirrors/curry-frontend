-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- GenFlatCurry - Generates FlatCurry program terms and FlatCurry interfaces
--                (type 'FlatCurry.Prog')
--
-- November 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module GenFlatCurry (genFlatCurry,
		     genFlatInterface) where


import Base (ArityEnv, ArityInfo(..), ModuleEnv, PEnv, PrecInfo(..), 
	     OpPrec(..), TCEnv, TypeInfo(..), ValueEnv, ValueInfo(..),
	     lookupValue, qualLookupTC,
	     qualLookupArity, lookupArity,  internalError)

import FlatCurry
import qualified IL
import qualified CurrySyntax as CS

import CurryEnv (CurryEnv)
import qualified CurryEnv

import ScopeEnv (ScopeEnv)
import qualified ScopeEnv

import Types
import CurryCompilerOpts
import Message
import PatchPrelude
import Position
import Ident
import TopEnv
import Env
import Map
import Monad
import Maybe


-------------------------------------------------------------------------------

-- transforms intermediate language code (IL) to FlatCurry code
genFlatCurry :: Options -> CurryEnv -> ModuleEnv -> ValueEnv -> TCEnv 
		-> ArityEnv -> IL.Module -> (Prog, [Message])
genFlatCurry opts cEnv mEnv tyEnv tcEnv aEnv mod
   = (patchPreludeFCY prog, messages)
 where (prog, messages) 
	   = run opts cEnv mEnv tyEnv tcEnv aEnv False (visitModule mod)


-- transforms intermediate language code (IL) to FlatCurry interfaces
genFlatInterface :: Options -> CurryEnv -> ModuleEnv -> ValueEnv -> TCEnv
		 -> ArityEnv -> IL.Module -> (Prog, [Message])
genFlatInterface opts cEnv mEnv tyEnv tcEnv aEnv mod
   = (patchPreludeFCY intf, messages)
 where (intf, messages) 
	   = run opts cEnv mEnv tyEnv tcEnv aEnv True (visitModule mod)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
visitModule :: IL.Module -> FlatState Prog
visitModule (IL.Module mid imps decls)
   = whenFlatCurry
       (do ops     <- genOpDecls
           datas   <- mapM visitDataDecl (filter isDataDecl decls)
	   types   <- genTypeSynonyms
	   records <- genRecordTypes
	   funcs   <- mapM visitFuncDecl (filter isFuncDecl decls)
	   mod     <- visitModuleIdent mid
	   imps'   <- imports
	   is      <- mapM visitModuleIdent 
	                   (map (\ (CS.IImportDecl _ mid) -> mid) imps')
           return (Prog mod is (records ++ types ++ datas) funcs ops))
       (do ops     <- genOpDecls
	   ds      <- filterM isPublicDataDecl decls
	   datas   <- mapM visitDataDecl ds
	   types   <- genTypeSynonyms
	   records <- genRecordTypes
	   fs      <- filterM isPublicFuncDecl decls
	   funcs   <- mapM visitFuncDecl fs
	   expimps <- getExportedImports
	   itypes  <- mapM visitTypeIDecl (filter isTypeIDecl expimps)
	   ifuncs  <- mapM visitFuncIDecl (filter isFuncIDecl expimps)
	   iops    <- mapM visitOpIDecl (filter isOpIDecl expimps)
	   mod     <- visitModuleIdent mid
	   imps'   <- imports
	   is      <- mapM visitModuleIdent 
	                   (map (\ (CS.IImportDecl _ mid) -> mid) imps')
	   return (Prog mod 
		        is 
		        (itypes ++ records ++ types ++ datas)
		        (ifuncs ++ funcs)
		        (iops ++ ops)))

--
visitDataDecl :: IL.Decl -> FlatState TypeDecl
visitDataDecl (IL.DataDecl qident arity constrs)
   = do cdecls <- mapM visitConstrDecl constrs
	qname  <- visitQualIdent qident
	vis    <- getVisibility qident
	return (Type qname vis [0 .. (arity - 1)] cdecls)
visitDataDecl _ = internalError "GenFlatCurry: no data declaration"

--
visitConstrDecl :: IL.ConstrDecl [IL.Type] -> FlatState ConsDecl
visitConstrDecl (IL.ConstrDecl qident types)
   = do texprs <- mapM visitType types
	qname  <- visitQualIdent qident
	vis    <- getVisibility qident
	return (Cons qname (length types) vis texprs)

--
visitType :: IL.Type -> FlatState TypeExpr
visitType (IL.TypeConstructor qident types)
   = do texprs <- mapM visitType types
	qname  <- visitQualIdent qident
	if (qualName qident) == "Identity"
	   then return (head texprs)
	   else return (TCons qname texprs)
visitType (IL.TypeVariable index)
   = return (TVar (int2num index))
visitType (IL.TypeArrow type1 type2)
   = do texpr1 <- visitType type1
	texpr2 <- visitType type2
	return (FuncType texpr1 texpr2)

--
visitFuncDecl :: IL.Decl -> FlatState FuncDecl
visitFuncDecl (IL.FunctionDecl qident params typeexpr expression)
   = whenFlatCurry
       (do setFunctionId qident
	   is    <- mapM newVarIndex params
	   texpr <- visitType typeexpr
	   expr  <- visitExpression expression
	   qname <- visitQualIdent qident
	   vis   <- getVisibility qident
	   clearVarIndices
	   return (Func qname (length params) vis texpr (Rule is expr)))
       (do setFunctionId qident
	   texpr <- visitType typeexpr
	   qname <- visitQualIdent qident
	   clearVarIndices
	   return (Func qname (length params) Public texpr (Rule [] (Var 0))))
visitFuncDecl (IL.ExternalDecl qident _ name typeexpr)
   = do setFunctionId qident
	texpr <- visitType typeexpr
	qname <- visitQualIdent qident
	vis   <- getVisibility qident
	xname <- visitExternalName name
	return (Func qname (typeArity typeexpr) vis texpr (External xname))
visitFuncDecl (IL.NewtypeDecl _ _ _)
   = do mid <- moduleId 
	error ("\"" ++ moduleName mid 
	       ++ "\": newtype declarations are not supported")
visitFuncDecl _ = internalError "GenFlatCurry: no function declaration"

--
visitExpression :: IL.Expression -> FlatState Expr
visitExpression (IL.Literal literal)
   = do lit <- visitLiteral literal
	return (Lit lit)
visitExpression (IL.Variable ident)
   = do index_ <- lookupVarIndex ident
	maybe (internalError (missingVarIndex ident))
	      (return . Var)
	      index_
visitExpression (IL.Function qident _)
   = do arity_ <- lookupIdArity qident
	maybe (internalError (funcArity qident))
	      (\arity -> genFuncCall qident arity [])
	      arity_
visitExpression (IL.Constructor qident arity)
   = do arity_ <- lookupIdArity qident
	maybe (internalError (consArity qident))
	      (\arity -> genConsCall qident arity [])
	      arity_
visitExpression (IL.Apply expression1 expression2)
   = genFlatApplication (IL.Apply expression1 expression2)
visitExpression (IL.Case evalannot expression alts)
   = do ea       <- visitEval evalannot
	expr     <- visitExpression expression
	branches <- mapM visitAlt alts
	return (Case ea expr branches)
visitExpression (IL.Or expression1 expression2)
   = do expr1 <- visitExpression expression1
	expr2 <- visitExpression expression2
	checkOverlapping expr1 expr2
	return (Or expr1 expr2)
visitExpression (IL.Exist ident expression)
   = do index <- newVarIndex ident
	expr  <- visitExpression expression
	case expr of
	  Free is expr' -> return (Free (index:is) expr')
	  _             -> return (Free [index] expr)
visitExpression (IL.Let binding expression)
   = do beginScope
	newVarIndex (bindingIdent binding)
        bind <- visitBinding binding
	expr <- visitExpression expression
	case expr of
	  Let binds expr' -> return (Let (bind:binds) expr')
	  _               -> return (Let [bind] expr)
visitExpression (IL.Letrec bindings expression)
   = do beginScope
	mapM_ newVarIndex (map bindingIdent bindings)
	binds <- mapM visitBinding bindings
	expr  <- visitExpression expression
	endScope
	return (Let binds expr)

--
visitLiteral :: IL.Literal -> FlatState Literal
visitLiteral (IL.Char c)  = return (Charc c)
visitLiteral (IL.Int i)   = return (Intc i)
visitLiteral (IL.Float f) = return (Floatc f)

--
visitAlt :: IL.Alt -> FlatState BranchExpr
visitAlt (IL.Alt cterm expression)
   = do patt <- visitConstrTerm cterm
	expr <- visitExpression expression
	return (Branch patt expr)

--
visitConstrTerm :: IL.ConstrTerm -> FlatState Pattern
visitConstrTerm (IL.LiteralPattern literal)
   = do lit <- visitLiteral literal
	return (LPattern lit)
visitConstrTerm (IL.ConstructorPattern qident args)
   = do is    <- mapM newVarIndex args
	qname <- visitQualIdent qident
	return (Pattern qname is)
visitConstrTerm (IL.VariablePattern ident)
   = do mid <- moduleId
	error ("\"" ++ moduleName mid 
	       ++ "\": variable patterns are not supported")

--
visitEval :: IL.Eval -> FlatState CaseType
visitEval IL.Rigid = return (Rigid)
visitEval IL.Flex  = return (Flex)

--
visitBinding :: IL.Binding -> FlatState (VarIndex, Expr)
visitBinding (IL.Binding ident expression)
   = do index_ <- lookupVarIndex ident
	index  <- maybe (internalError (missingVarIndex ident))
		  return
		  index_
	expr   <- visitExpression expression
	return (index, expr)


-------------------------------------------------------------------------------

--
visitFuncIDecl :: CS.IDecl -> FlatState FuncDecl
visitFuncIDecl (CS.IFunctionDecl _ qident arity typeexpr)
   = do texpr <- visitType (fst (cs2ilType [] typeexpr))
	qname <- visitQualIdent qident
	return (Func qname arity Public texpr (Rule [] (Var 0)))
visitFuncIDecl _ = internalError "GenFlatCurry: no function interface"

--
visitTypeIDecl :: CS.IDecl -> FlatState TypeDecl
visitTypeIDecl (CS.IDataDecl _ qident params constrs_)
   = do let mid = fromMaybe (internalError "GenFlatCurry: no module name")
		            (fst (splitQualIdent qident))
	    is  = [0 .. (length params) - 1]
	cdecls <- mapM (visitConstrIDecl mid (zip params is)) 
		       (catMaybes constrs_)
	qname  <- visitQualIdent qident
	return (Type qname Public is cdecls)
visitTypeIDecl (CS.ITypeDecl _ qident params typeexpr)
   = do let is = [0 .. (length params) - 1]
	texpr <- visitType (fst (cs2ilType (zip params is) typeexpr))
	qname <- visitQualIdent qident
	return (TypeSyn qname Public is texpr)
visitTypeIDecl _ = internalError "GenFlatCurry: no type interface"

--
visitConstrIDecl :: ModuleIdent -> [(Ident, Int)] -> CS.ConstrDecl 
		    -> FlatState ConsDecl
visitConstrIDecl mid tis (CS.ConstrDecl _ _ ident typeexprs)
   = do texprs <- mapM visitType (map (fst . cs2ilType tis) typeexprs)
	qname  <- visitQualIdent (qualifyWith mid ident)
	return (Cons qname (length typeexprs) Public texprs)
visitConstrIDecl mid tis (CS.ConOpDecl pos ids type1 ident type2)
   = visitConstrIDecl mid tis (CS.ConstrDecl pos ids ident [type1,type2])

--
visitOpIDecl :: CS.IDecl -> FlatState OpDecl
visitOpIDecl (CS.IInfixDecl _ fixity prec qident)
   = do let fix = case fixity of
	            CS.InfixL -> InfixlOp
		    CS.InfixR -> InfixrOp
		    _         -> InfixOp
        qname <- visitQualIdent qident
	return (Op qname fix prec)


-------------------------------------------------------------------------------

--
visitModuleIdent :: ModuleIdent -> FlatState String
visitModuleIdent mident = return (moduleName mident)

--
visitQualIdent :: QualIdent -> FlatState QName
visitQualIdent qident
   = do mid <- moduleId
	let (mmod, ident) = splitQualIdent qident
	    mod | elem ident [listId, consId, nilId, unitId] || isTupleId ident
		  = moduleName preludeMIdent
		| otherwise
		  = maybe (moduleName mid) moduleName mmod
	return (mod, name ident)

--
visitExternalName :: String -> FlatState String
visitExternalName name 
   = moduleId >>= (\mid -> return ((moduleName mid) ++ "." ++ name))


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
getVisibility :: QualIdent -> FlatState Visibility
getVisibility qident
   = do public <- isPublic qident
	if public then return Public else return Private


--
getExportedImports :: FlatState [CS.IDecl]
getExportedImports
   = do mid  <- moduleId
	exps <- exports
	genExportedIDecls (envToList (getExpImports mid emptyEnv exps))

--
getExpImports :: ModuleIdent -> Env ModuleIdent [CS.Export] -> [CS.Export]
		 -> Env ModuleIdent [CS.Export]
getExpImports mident expenv [] = expenv
getExpImports mident expenv ((CS.Export qident):exps)
   = getExpImports mident 
	           (bindExpImport mident qident (CS.Export qident) expenv) 
		   exps
getExpImports mident expenv ((CS.ExportTypeWith qident idents):exps)
   = getExpImports mident 
		   (bindExpImport mident 
		                  qident 
		                  (CS.ExportTypeWith qident idents) 
		                  expenv)
		   exps
getExpImports mident expenv ((CS.ExportTypeAll qident):exps)
   = getExpImports mident 
	 	   (bindExpImport mident qident (CS.ExportTypeAll qident) expenv) 
		   exps
getExpImports mident expenv ((CS.ExportModule mident'):exps)
   = getExpImports mident (bindEnv mident' [] expenv) exps

--
bindExpImport :: ModuleIdent -> QualIdent -> CS.Export 
	         -> Env ModuleIdent [CS.Export] -> Env ModuleIdent [CS.Export]
bindExpImport mident qident export expenv
   | isJust (localIdent mident qident)
     = expenv
   | otherwise
     = let (mmod, _) = splitQualIdent qident
	   mod       = fromJust mmod
       in  maybe (bindEnv mod [export] expenv)
	         (\es -> bindEnv mod (export:es) expenv) 
		 (lookupEnv mod expenv)

--
genExportedIDecls :: [(ModuleIdent,[CS.Export])] -> FlatState [CS.IDecl]
genExportedIDecls mes = genExpIDecls [] mes

--
genExpIDecls :: [CS.IDecl] -> [(ModuleIdent,[CS.Export])] -> FlatState [CS.IDecl]
genExpIDecls idecls [] = return idecls
genExpIDecls idecls ((mid,exps):mes)
   = do intf_ <- lookupModuleIntf mid
	let idecls' = maybe idecls (p_genExpIDecls mid idecls exps) intf_
	genExpIDecls idecls' mes
 where
   p_genExpIDecls mid idecls exps intf
      | null exps = (map (qualifyIDecl mid) intf) ++ idecls
      | otherwise = (filter (isExportedIDecl exps) 
		            (map (qualifyIDecl mid) intf))
		    ++ idecls

-- 
isExportedIDecl :: [CS.Export] -> CS.IDecl -> Bool
isExportedIDecl exports (CS.IInfixDecl _ _ _ qident)
   = isExportedQualIdent qident exports
isExportedIDecl exports (CS.IDataDecl _ qident _ _)
   = isExportedQualIdent qident exports
isExportedIDecl exports (CS.ITypeDecl _ qident _ _)
   = isExportedQualIdent qident exports
isExportedIDecl exports (CS.IFunctionDecl _ qident _ _)
   = isExportedQualIdent qident exports
isExportedIDecl exports _
   = False

--
isExportedQualIdent :: QualIdent -> [CS.Export] -> Bool
isExportedQualIdent qident [] = False
isExportedQualIdent qident ((CS.Export qident'):exps)
   = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((CS.ExportTypeWith qident' idents):exps)
   = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((CS.ExportTypeAll qident'):exps)
   = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((CS.ExportModule _):exps)
   = isExportedQualIdent qident exps

--
qualifyIDecl :: ModuleIdent -> CS.IDecl -> CS.IDecl
qualifyIDecl mident (CS.IInfixDecl pos fix prec qident)
   = (CS.IInfixDecl pos fix prec (qualQualify mident qident))
qualifyIDecl mident (CS.IDataDecl pos qident idents cdecls)
   = (CS.IDataDecl pos (qualQualify mident qident) idents cdecls)
qualifyIDecl mident (CS.INewtypeDecl pos qident idents ncdecl)
   = (CS.INewtypeDecl pos (qualQualify mident qident) idents ncdecl)
qualifyIDecl mident (CS.ITypeDecl pos qident idents texpr)
   = (CS.ITypeDecl pos (qualQualify mident qident) idents texpr)
qualifyIDecl mident (CS.IFunctionDecl pos qident arity texpr)
   = (CS.IFunctionDecl pos (qualQualify mident qident) arity texpr)
qualifyIDecl _ idecl = idecl


--
typeArity :: IL.Type -> Int
typeArity (IL.TypeArrow _ t)       = 1 + (typeArity t)
typeArity (IL.TypeConstructor _ _) = 0
typeArity (IL.TypeVariable _)      = 0


-------------------------------------------------------------------------------

--
genFlatApplication :: IL.Expression -> FlatState Expr
genFlatApplication applicexpr
   = genFlatApplic [] applicexpr
 where
   genFlatApplic args expression 
      = case expression of
	  (IL.Apply expr1 expr2)    
	      -> genFlatApplic (expr2:args) expr1
	  (IL.Function qident _)
	      -> do arity_ <- lookupIdArity qident
		    maybe (internalError (funcArity qident))
			  (\arity -> genFuncCall qident arity args)
			  arity_
	  (IL.Constructor qident _)
	      -> do arity_ <- lookupIdArity qident
		    maybe (internalError (consArity qident))
			  (\arity -> genConsCall qident arity args)
			  arity_
	  _   -> do expr <- visitExpression expression
		    genApplicComb expr args

--
genFuncCall :: QualIdent -> Int -> [IL.Expression] -> FlatState Expr
genFuncCall qident arity args
   | arity > cnt 
     = genComb qident args (FuncPartCall (arity - cnt))
   | arity < cnt 
     = do let (funcargs, applicargs) = splitAt arity args
	  funccall <- genComb qident funcargs FuncCall
	  genApplicComb funccall applicargs
   | otherwise   
     = genComb qident args FuncCall
 where cnt = length args

--
genConsCall :: QualIdent -> Int -> [IL.Expression] -> FlatState Expr
genConsCall qident arity args
   | arity > cnt 
     = genComb qident args (ConsPartCall (arity - cnt))
   | arity < cnt
     = do let (funcargs, applicargs) = splitAt arity args
	  conscall <- genComb qident funcargs ConsCall
	  genApplicComb conscall applicargs
   | otherwise 
     = genComb qident args ConsCall 
 where cnt = length args

--
genComb :: QualIdent -> [IL.Expression] -> CombType -> FlatState Expr
genComb qident args combtype
   = do exprs <- mapM visitExpression args
	qname <- visitQualIdent qident
	return (Comb combtype qname exprs)
	 
--
genApplicComb :: Expr -> [IL.Expression] -> FlatState Expr
genApplicComb expr [] = return expr
genApplicComb expr (e1:es)
   = do expr1 <- visitExpression e1
	qname <- visitQualIdent qidApply
	genApplicComb (Comb FuncCall qname [expr, expr1]) es
 where
 qidApply = qualifyWith preludeMIdent (mkIdent "apply")


--
genOpDecls :: FlatState [OpDecl]
genOpDecls = fixities >>= (\fix -> mapM genOpDecl fix)

--
genOpDecl :: CS.IDecl -> FlatState OpDecl
genOpDecl (CS.IInfixDecl _ fixity prec qident)
   = do qname <- visitQualIdent qident
	return (Op qname (p_genOpFixity fixity) prec)
 where
   p_genOpFixity CS.InfixL = InfixlOp
   p_genOpFixity CS.InfixR = InfixrOp
   p_genOpFixity CS.Infix  = InfixOp
genOpDecl _ = internalError "GenFlatCurry: no infix interface"


--
genTypeSynonyms ::  FlatState [TypeDecl]
genTypeSynonyms = typeSynonyms >>= mapM genTypeSynonym

--
genTypeSynonym :: CS.IDecl -> FlatState TypeDecl
genTypeSynonym (CS.ITypeDecl _ qident params typeexpr)
   = do let is = [0 .. (length params) - 1]
        (tyEnv,tcEnv) <- environments
	let typeexpr' = elimRecordTypes tyEnv tcEnv typeexpr
	texpr <- visitType (fst (cs2ilType (zip params is) typeexpr'))
	qname <- visitQualIdent qident
	vis   <- getVisibility qident
	return (TypeSyn qname vis is texpr)
genTypeSynonym _ = internalError "GenFlatCurry: no type synonym interface"


-- In order to provide interfaces for record declarations, 'genRecordTypes'
-- generates dummy data declarations representing records and together
-- with their typed labels.
-- Note: These dummies should occur in the FlatCurry interface as well as
-- in the corresponding FlatCurry program.
genRecordTypes :: FlatState [TypeDecl]
genRecordTypes = records >>= mapM genRecordType

--
genRecordType :: CS.IDecl -> FlatState TypeDecl
genRecordType (CS.ITypeDecl _ qident params (CS.RecordType fields _))
   = do let is = [0 .. (length params) - 1]
	    (mod,ident) = splitQualIdent qident
	qname <- visitQualIdent ((maybe qualify qualifyWith mod) 
				 (recordExtId ident))
	labels <- mapM (genRecordLabel mod (zip params is)) fields
	return (Type qname Public is labels)

--
genRecordLabel :: Maybe ModuleIdent -> [(Ident,Int)] -> ([Ident],CS.TypeExpr) 
	       -> FlatState ConsDecl
genRecordLabel mod vis ([ident],typeexpr)
   = do (tyEnv,tcEnv) <- environments
	let typeexpr' = elimRecordTypes tyEnv tcEnv typeexpr
        texpr <- visitType (fst (cs2ilType vis typeexpr'))
	qname <- visitQualIdent ((maybe qualify qualifyWith mod) 
				 (labelExtId ident))
	return (Cons qname 1 Public [texpr])


-------------------------------------------------------------------------------

--
elimRecordTypes :: ValueEnv -> TCEnv -> CS.TypeExpr -> CS.TypeExpr
elimRecordTypes tyEnv tcEnv (CS.ConstructorType qid typeexprs)
   = CS.ConstructorType qid (map (elimRecordTypes tyEnv tcEnv) typeexprs)
elimRecordTypes tyEnv tcEnv (CS.VariableType id)
   = CS.VariableType id
elimRecordTypes tyEnv tcEnv (CS.TupleType typeexprs)
   = CS.TupleType (map (elimRecordTypes tyEnv tcEnv) typeexprs)
elimRecordTypes tyEnv tcEnv (CS.ListType typeexpr)
   = CS.ListType (elimRecordTypes tyEnv tcEnv typeexpr)
elimRecordTypes tyEnv tcEnv (CS.ArrowType typeexpr1 typeexpr2)
   = CS.ArrowType (elimRecordTypes tyEnv tcEnv typeexpr1)
                  (elimRecordTypes tyEnv tcEnv typeexpr2)
elimRecordTypes tyEnv tcEnv (CS.RecordType fss _)
   = let fs = flattenRecordTypeFields fss
     in  case (lookupValue (fst (head fs)) tyEnv) of
  	   [Label _ record _] ->
	     case (qualLookupTC record tcEnv) of
	       [AliasType _ n (TypeRecord fs' _)] ->
	         let ms = foldl (matchTypeVars fs) zeroFM fs'
		     types = map (\i -> maybe 
			 	          (CS.VariableType 
					     (mkIdent ("#tvar" ++ show i)))
				          (elimRecordTypes tyEnv tcEnv)
				          (lookupFM i ms))
			         [0 .. n-1]
	         in  CS.ConstructorType record types
	       _ -> internalError ("GenFlatCurry.elimRecordTypes: "
		 		   ++ "no record type")
	   _ -> internalError ("GenFlatCurry.elimRecordTypes: "
			       ++ "no label")

matchTypeVars :: [(Ident,CS.TypeExpr)] -> FM Int CS.TypeExpr
	      -> (Ident, Type) -> FM Int CS.TypeExpr
matchTypeVars fs ms (l,ty)
   = maybe ms (match ms ty) (lookup l fs)
  where
  match ms (TypeVariable i) typeexpr = addToFM i typeexpr ms
  match ms (TypeConstructor _ tys) (CS.ConstructorType _ typeexprs)
     = matchList ms tys typeexprs
  match ms (TypeConstructor _ tys) (CS.ListType typeexpr)
     = matchList ms tys [typeexpr]
  match ms (TypeConstructor _ tys) (CS.TupleType typeexprs)
     = matchList ms tys typeexprs
  match ms (TypeArrow ty1 ty2) (CS.ArrowType typeexpr1 typeexpr2)
     = matchList ms [ty1,ty2] [typeexpr1,typeexpr2]
  match ms (TypeRecord fs' _) (CS.RecordType fss _)
     = foldl (matchTypeVars (flattenRecordTypeFields fss)) ms fs'
  match ms ty typeexpr
     = internalError ("GenFlatCurry.matchTypeVars: "
		      ++ show ty ++ "\n" ++ show typeexpr)

  matchList ms tys typeexprs
     = foldl (\ms' (ty,typeexpr) -> match ms' ty typeexpr)
             ms
	     (zip tys typeexprs)


flattenRecordTypeFields :: [([Ident],CS.TypeExpr)] -> [(Ident,CS.TypeExpr)]
flattenRecordTypeFields fss
   = concatMap (\ (labels, typeexpr)
		-> map (\label -> (label,typeexpr)) labels)
               fss

-------------------------------------------------------------------------------

--
checkOverlapping :: Expr -> Expr -> FlatState ()
checkOverlapping expr1 expr2
   = do opts <- compilerOpts
	unless (noOverlapWarn opts)
	       (checkOverlap expr1 expr2)
 where
 checkOverlap (Case _ _ _) _ 
    = do qid <- functionId
	 genWarning (overlappingRules qid)
 checkOverlap _ (Case _ _ _)
    = do qid <- functionId
	 genWarning (overlappingRules qid)
 checkOverlap _ _ = return ()


-------------------------------------------------------------------------------

-- 
cs2ilType :: [(Ident,Int)] -> CS.TypeExpr -> (IL.Type, [(Ident,Int)])
cs2ilType ids (CS.ConstructorType qident typeexprs)
   = let (ilTypeexprs, ids') = emap cs2ilType ids typeexprs
     in  (IL.TypeConstructor qident ilTypeexprs, ids')
cs2ilType ids (CS.VariableType ident)
   = let mid        = lookup ident ids
	 nid        | null ids  = 0
		    | otherwise = 1 + snd (head ids)
	 (id, ids') | isJust mid = (fromJust mid, ids)
		    | otherwise  = (nid, (ident, nid):ids)
     in  (IL.TypeVariable id, ids')
cs2ilType ids (CS.ArrowType type1 type2)
   = let (ilType1, ids')  = cs2ilType ids type1
	 (ilType2, ids'') = cs2ilType ids' type2
     in  (IL.TypeArrow ilType1 ilType2, ids'')
cs2ilType ids (CS.ListType typeexpr)
   = let (ilTypeexpr, ids') = cs2ilType ids typeexpr
     in  (IL.TypeConstructor (qualify listId) [ilTypeexpr], ids')
cs2ilType ids (CS.TupleType typeexprs)
   | null typeexprs
     = (IL.TypeConstructor qUnitId [], ids)
   | otherwise
     = let (ilTypeexprs, ids') = emap cs2ilType ids typeexprs
       in  (IL.TypeConstructor (qTupleId ((length ilTypeexprs) - 1)) ilTypeexprs,
            ids')
cs2ilType _ typeexpr = internalError ("cs2ilType: " ++ show typeexpr)


-------------------------------------------------------------------------------
-- Messages for internal errors and warnings

funcArity qid = "GenFlatCurry: missing arity for function \"" 
		++ show qid ++ "\""

consArity qid = "GenFlatCurry: missing arity for constructor \""
		++ show qid ++ "\""

missingVarIndex id = "GenFlatCurry: missing index for \"" ++ show id ++ "\""


overlappingRules qid = (OverlapRules,
                           "function \""
		        ++ show qid 
		        ++ "\" is non-deterministic due to non-trivial "
		        ++ "overlapping rules")


-------------------------------------------------------------------------------

prelude_types :: [TypeDecl]
prelude_types = [(Type ("Prelude","()") Public [] 
		  [(Cons ("Prelude","()") 0 Public [])]),
		 (Type ("Prelude","[]") Public [0] 
		  [(Cons ("Prelude","[]") 0 Public []),
		   (Cons ("Prelude",":") 2 Public 
		    [(TVar 0),(TCons ("Prelude","[]") [(TVar 0)])])]),
		 (Type ("Prelude","(,)") Public [0,1] 
		  [(Cons ("Prelude","(,)") 2 Public [(TVar 0),(TVar 1)])]),
		 (Type ("Prelude","(,,)") Public [0,1,2]
		  [(Cons ("Prelude","(,,)") 3 Public 
		    [(TVar 0),(TVar 1),(TVar 2)])]),
		 (Type ("Prelude","(,,,)") Public [0,1,2,3] 
		  [(Cons ("Prelude","(,,,)") 4 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3)])]),
		 (Type ("Prelude","(,,,,)") Public [0,1,2,3,4] 
		  [(Cons ("Prelude","(,,,,)") 5 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),(TVar 4)])]),
		 (Type ("Prelude","(,,,,,)") Public [0,1,2,3,4,5] 
		  [(Cons ("Prelude","(,,,,,)") 6 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),(TVar 4),(TVar 5)])]),
		 (Type ("Prelude","(,,,,,,)") Public [0,1,2,3,4,5,6] 
		  [(Cons ("Prelude","(,,,,,,)") 7 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6)])]),
		 (Type ("Prelude","(,,,,,,,)") Public [0,1,2,3,4,5,6,7] 
		  [(Cons ("Prelude","(,,,,,,,)") 8 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7)])]),
		 (Type ("Prelude","(,,,,,,,,)") Public [0,1,2,3,4,5,6,7,8] 
		  [(Cons ("Prelude","(,,,,,,,,)") 9 Public
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8)])]),
		 (Type ("Prelude","(,,,,,,,,,)") Public [0,1,2,3,4,5,6,7,8,9] 
		  [(Cons ("Prelude","(,,,,,,,,,)") 10 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),(TVar 9)])]),
		 (Type ("Prelude","(,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10] 
		  [(Cons ("Prelude","(,,,,,,,,,,)") 11 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),
		     (TVar 9),(TVar 10)])]),
		 (Type ("Prelude","(,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11] 
		  [(Cons ("Prelude","(,,,,,,,,,,,)") 12 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),
		     (TVar 9),(TVar 10),(TVar 11)])]),
		 (Type ("Prelude","(,,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11,12] 
		  [(Cons ("Prelude","(,,,,,,,,,,,,)") 13 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),
		     (TVar 8),(TVar 9),(TVar 10),(TVar 11),(TVar 12)])]),
		 (Type ("Prelude","(,,,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11,12,13] 
		  [(Cons ("Prelude","(,,,,,,,,,,,,,)") 14 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),
		     (TVar 8),(TVar 9),(TVar 10),(TVar 11),
		     (TVar 12),(TVar 13)])]),
		 (Type ("Prelude","(,,,,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] 
		  [(Cons ("Prelude","(,,,,,,,,,,,,,,)") 15 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),
		     (TVar 8),(TVar 9),(TVar 10),(TVar 11),
		     (TVar 12),(TVar 13),(TVar 14)])])]


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
isDataDecl :: IL.Decl -> Bool
isDataDecl (IL.DataDecl _ _ _) = True
isDataDecl _                = False

--
isFuncDecl :: IL.Decl -> Bool
isFuncDecl (IL.FunctionDecl _ _ _ _) = True
isFuncDecl (IL.ExternalDecl _ _ _ _) = True
isFuncDecl _                         = False

--
isPublicDataDecl :: IL.Decl -> FlatState Bool
isPublicDataDecl (IL.DataDecl qident _ _ ) = isPublic qident
isPublicDataDecl _                         = return False

--
isPublicFuncDecl :: IL.Decl -> FlatState Bool
isPublicFuncDecl (IL.FunctionDecl qident _ _ _) = isPublic qident
isPublicFuncDecl (IL.ExternalDecl qident _ _ _) = isPublic qident
isPublicFuncDecl _                              = return False

--
isTypeIDecl :: CS.IDecl -> Bool
isTypeIDecl (CS.IDataDecl _ _ _ _) = True
isTypeIDecl (CS.ITypeDecl _ _ _ _) = True
isTypeIDecl _                      = False

--
isRecordIDecl :: CS.IDecl -> Bool
isRecordIDecl (CS.ITypeDecl _ _ _ (CS.RecordType _ _)) = True
isRecordIDecl _                                        = False

--
isFuncIDecl :: CS.IDecl -> Bool
isFuncIDecl (CS.IFunctionDecl _ _ _ _) = True
isFuncIDecl _                          = False

--
isOpIDecl :: CS.IDecl -> Bool
isOpIDecl (CS.IInfixDecl _ _ _ _) = True
isOpIDecl _                       = False 


--
bindingIdent :: IL.Binding -> Ident
bindingIdent (IL.Binding ident _) = ident

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

int2num :: Int -> Int
int2num i | i < 0     = (-1) * i
	  | otherwise = i


emap :: (e -> a -> (b,e)) -> e -> [a] -> ([b], e)
emap _ env []     = ([], env)
emap f env (x:xs) = let (x',env')    = f env x
			(xs', env'') = emap f env' xs
		    in  ((x':xs'), env'')

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for representing an environment which contains information needed
-- for generating FlatCurry code.
data FlatEnv a = FlatEnv{ moduleIdE     :: ModuleIdent,
			  functionIdE   :: QualIdent,
			  compilerOptsE :: Options,
			  moduleEnvE    :: ModuleEnv,
			  arityEnvE     :: ArityEnv,
			  typeEnvE      :: ValueEnv,
			  tConsEnvE     :: TCEnv,
			  publicEnvE    :: Env Ident Bool,
			  fixitiesE     :: [CS.IDecl],
			  typeSynonymsE :: [CS.IDecl],
			  importsE      :: [CS.IDecl],
			  exportsE      :: [CS.Export],
			  interfaceE    :: [CS.IDecl],
			  varIndexE     :: Int,
			  varIdsE       :: ScopeEnv Ident Int,
			  tvarIndexE    :: Int,
			  tvarIdsE      :: ScopeEnv Ident Int,
			  messagesE     :: [Message],
			  genInterfaceE :: Bool,
			  result        :: a
			}



-- The environment 'FlatEnv' is embedded in the monadic representation
-- 'FlatState' which allows the usage of 'do' expressions.
data FlatState a = FlatState (FlatEnv () -> FlatEnv a)

instance Monad FlatState where

   -- (>>=)
   (FlatState f) >>= g = FlatState (\env -> let env'        = f env
				                FlatState h = g (result env')
				            in  h (env'{ result = () }))

   -- (>>)
   a >> b = a >>= (\_ -> b)

   -- return
   return v = FlatState (\env -> env{ result = v })


-- Runs a 'FlatState' action an returns the result
run :: Options -> CurryEnv -> ModuleEnv -> ValueEnv -> TCEnv -> ArityEnv 
    -> Bool -> FlatState a -> (a, [Message])
run opts cEnv mEnv tyEnv tcEnv aEnv genIntf (FlatState f)
   = (result env, messagesE env)
 where
 env = f (FlatEnv{ moduleIdE     = CurryEnv.moduleId cEnv,
		   functionIdE   = qualify (mkIdent ""),
		   compilerOptsE = opts,
		   moduleEnvE    = mEnv,
		   arityEnvE     = aEnv,
		   typeEnvE      = tyEnv,
		   tConsEnvE     = tcEnv,
		   publicEnvE    = genPubEnv (CurryEnv.moduleId cEnv)
		                             (CurryEnv.interface cEnv),
		   fixitiesE     = CurryEnv.infixDecls cEnv,
		   typeSynonymsE = CurryEnv.typeSynonyms cEnv,
		   importsE      = CurryEnv.imports cEnv,
		   exportsE      = CurryEnv.exports cEnv,
		   interfaceE    = CurryEnv.interface cEnv,
		   varIndexE     = 0,
		   varIdsE       = ScopeEnv.new,
		   tvarIndexE    = 0,
		   tvarIdsE      = ScopeEnv.new,
		   messagesE      = [],
		   genInterfaceE = genIntf,
		   result        = ()
		 } )


--
moduleId :: FlatState ModuleIdent
moduleId = FlatState (\env -> env{ result = moduleIdE env })

--
functionId :: FlatState QualIdent
functionId = FlatState (\env -> env{ result = functionIdE env })

--
setFunctionId :: QualIdent -> FlatState ()
setFunctionId qid = FlatState (\env -> env{ functionIdE = qid })

--
compilerOpts :: FlatState Options
compilerOpts = FlatState (\env -> env{ result = compilerOptsE env })

--
exports :: FlatState [CS.Export]
exports = FlatState (\env -> env{ result = exportsE env })

--
imports :: FlatState [CS.IDecl]
imports = FlatState (\env -> env{ result = importsE env })

--
records :: FlatState [CS.IDecl]
records 
   = FlatState 
       (\env -> env{ result = filter isRecordIDecl (interfaceE env) })

--
fixities :: FlatState [CS.IDecl]
fixities = FlatState (\env -> env{ result = fixitiesE env })

--
typeSynonyms :: FlatState [CS.IDecl]
typeSynonyms = FlatState (\env -> env{ result = typeSynonymsE env })

--
environments :: FlatState (ValueEnv,TCEnv)
environments 
   = FlatState 
       (\env -> env{ result = (typeEnvE env, tConsEnvE env) })

--
isPublic :: QualIdent -> FlatState Bool
isPublic qid
   = FlatState
       (\env -> env{ result = fromMaybe False
		                        (lookupEnv (unqualify qid) 
					           (publicEnvE env))
		   })

--
lookupModuleIntf :: ModuleIdent -> FlatState (Maybe [CS.IDecl])
lookupModuleIntf mid
   = FlatState (\env -> env{ result = lookupEnv mid (moduleEnvE env) })

--
lookupIdArity :: QualIdent -> FlatState (Maybe Int)
lookupIdArity qid
   = FlatState (\env -> env{ result = lookupA qid (arityEnvE env) })
 where
 lookupA qid aEnv = case (qualLookupArity qid aEnv) of
		      [ArityInfo _ a]
		         -> Just a
		      [] -> case (lookupArity (unqualify qid) aEnv) of
			      [ArityInfo _ a] -> Just a
			      _               -> Nothing
		      _  -> Nothing

-- Generates a new index for a variable
newVarIndex :: Ident -> FlatState Int
newVarIndex id
   = FlatState (\env -> let idx  = 1 + varIndexE env
		            vids = varIdsE env
		        in  env{ varIndexE = idx,
				 varIdsE   = ScopeEnv.insert id idx vids,
				 result    = idx
			       })

-- Looks up the index of an existing variable or generates a new index,
-- if the variable doesn't exist
getVarIndex :: Ident -> FlatState Int
getVarIndex id
   = FlatState 
       (\env -> let idx   = 1 + varIndexE env
	            vids  = varIdsE env    
	        in  maybe (env{ varIndexE = idx,
				varIdsE   = ScopeEnv.insert id idx vids,
				result    = idx})
	                  (\idx' -> env{ result = idx' })
	                  (ScopeEnv.lookup id vids))

--
lookupVarIndex :: Ident -> FlatState (Maybe Int)
lookupVarIndex id
   = FlatState (\env -> env{ result = ScopeEnv.lookup id (varIdsE env) })

--
clearVarIndices :: FlatState ()
clearVarIndices = FlatState (\env -> env{ varIndexE = 0,
					  varIdsE = ScopeEnv.new 
					})

-- Generates a new index for a type variable
newTVarIndex :: Ident -> FlatState Int
newTVarIndex id
   = FlatState (\env -> let idx  = 1 + tvarIndexE env
		            vids = tvarIdsE env
		        in  env{ tvarIndexE = idx,
				 tvarIdsE   = ScopeEnv.insert id idx vids,
				 result     = idx
			       })

-- Looks up the index of an existing type variable or generates a new index,
-- if the type variable doesn't exist
getTVarIndex :: Ident -> FlatState Int
getTVarIndex id
   = FlatState 
       (\env -> let idx   = 1 + tvarIndexE env
	            vids  = tvarIdsE env    
	        in  maybe (env{ tvarIndexE = idx,
				tvarIdsE   = ScopeEnv.insert id idx vids,
				result     = idx})
	                  (\idx' -> env{ result = idx' })
	                  (ScopeEnv.lookup id vids))

--
lookupTVarIndex :: Ident -> FlatState (Maybe Int)
lookupTVarIndex id
   = FlatState (\env -> env{ result = ScopeEnv.lookup id (tvarIdsE env) })

--
clearTVarIndices :: FlatState ()
clearTVarIndices = FlatState (\env -> env{ tvarIndexE = 0,
					   tvarIdsE = ScopeEnv.new 
					 })

--
genWarning :: (WarningType,String) -> FlatState ()
genWarning (warnType,msg)
   = FlatState (\env -> env{ messagesE = warnMsg:(messagesE env) })
 where warnMsg = message_ (Warning warnType) msg

--
genInterface :: FlatState Bool
genInterface = FlatState (\env -> env{ result = genInterfaceE env })

--
beginScope :: FlatState ()
beginScope = FlatState 
	       (\env -> env{ varIdsE  = ScopeEnv.beginScope (varIdsE env),
			     tvarIdsE = ScopeEnv.beginScope (tvarIdsE env)
			   })

--
endScope :: FlatState ()
endScope = FlatState 
	     (\env -> env{ varIdsE  = ScopeEnv.endScope (varIdsE env),
			   tvarIdsE = ScopeEnv.endScope (tvarIdsE env)
			 })

--
whenFlatCurry :: FlatState a -> FlatState a -> FlatState a
whenFlatCurry genFlat genIntf 
   = genInterface >>= (\intf -> if intf then genIntf else genFlat)


-------------------------------------------------------------------------------

-- Generates an evironment containing all public identifiers from the module
-- Note: Currently the record functions (selection and update) for all public 
-- record labels are inserted into the environment, though they are not
-- explicitly declared in the export specifications.
genPubEnv :: ModuleIdent -> [CS.IDecl] -> Env Ident Bool
genPubEnv mid idecls = foldl (bindEnvIDecl mid) emptyEnv idecls

--
bindEnvIDecl :: ModuleIdent -> Env Ident Bool -> CS.IDecl -> Env Ident Bool
bindEnvIDecl mid env (CS.IDataDecl _ qid _ mcdecls)
   = maybe env 
           (\id -> foldl bindEnvConstrDecl
	                 (bindEnv id True env)
	                 (catMaybes mcdecls))
	   (localIdent mid qid)
bindEnvIDecl mid env (CS.INewtypeDecl _ qid _ ncdecl)
   = maybe env 
           (\id -> bindEnvNewConstrDecl (bindEnv id True env) ncdecl)
	   (localIdent mid qid)
bindEnvIDecl mid env (CS.ITypeDecl _ qid _ texpr)
   = maybe env (\id -> bindEnvITypeDecl env id texpr) (localIdent mid qid)
bindEnvIDecl mid env (CS.IFunctionDecl _ qid _ _)
   = maybe env (\id -> bindEnv id True env) (localIdent mid qid)
bindEnvIDecl _ env _ = env

--
bindEnvITypeDecl :: Env Ident Bool -> Ident -> CS.TypeExpr
		    -> Env Ident Bool
bindEnvITypeDecl env id (CS.RecordType fs _)
   = bindEnv id True (foldl (bindEnvRecordLabel id) env fs)
bindEnvITypeDecl env id texpr
   = bindEnv id True env

--
bindEnvConstrDecl :: Env Ident Bool -> CS.ConstrDecl -> Env Ident Bool
bindEnvConstrDecl env (CS.ConstrDecl _ _ id _)  = bindEnv id True env
bindEnvConstrDecl env (CS.ConOpDecl _ _ _ id _) = bindEnv id True env

--
bindEnvNewConstrDecl :: Env Ident Bool -> CS.NewConstrDecl -> Env Ident Bool
bindEnvNewConstrDecl env (CS.NewConstrDecl _ _ id _) = bindEnv id True env

--
bindEnvRecordLabel :: Ident -> Env Ident Bool -> ([Ident],CS.TypeExpr) 
		   -> Env Ident Bool
bindEnvRecordLabel rec env ([lab],_)
   = bindEnv (recSelectorId (qualify rec) lab)
             True
	     (bindEnv (recUpdateId (qualify rec) lab) True env)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
