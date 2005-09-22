-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- IL2FlatCurry - Generates FlatCurry program terms and FlatCurry interfaces
--                (type 'FlatCurry.Prog')
--
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module IL2FlatCurry (il2flatCurry,
		     il2flatInterface) where

import IL
import Ident
import Base (ModuleEnv, ArityEnv, ArityInfo(..), 
	     qualLookupArity, lookupArity, internalError)
import TopEnv
import Env
import CurryInfo
import FlatCurry hiding (Literal, Expr(Or, Case, Let), CaseType(..))
import qualified FlatCurry (Literal, Expr(Or, Case, Let), CaseType(..))
import qualified CurrySyntax hiding (Export(..))
import CurrySyntax (Export(..))
import PatchPrelude
import Maybe

-------------------------------------------------------------------------------

-- transforms intermediate language code (IL) to FlatCurry code
il2flatCurry :: CurryInfo -> ModuleEnv -> ArityEnv -> Module -> Prog
il2flatCurry info mEnv aEnv mod 
   = patchPreludeFCY (fst (visitModule env mod))
 where
 env = initFlatEnv {moduleId     = getModuleIdent mod,
		    curryInfo    = info,
		    moduleEnv    = mEnv,
		    arityEnv     = aEnv,
	            genInterface = False}


-- transforms intermediate language code (IL) to FlatCurry interfaces
il2flatInterface :: CurryInfo -> ModuleEnv -> Module -> Prog
il2flatInterface info mEnv mod
   = patchPreludeFCY (fst (visitModule env mod))
 where
 env = initFlatEnv {moduleId     = getModuleIdent mod,
		    curryInfo    = info,
		    moduleEnv    = mEnv,
	            genInterface = True}


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
visitModule :: FlatEnv -> Module -> (Prog, FlatEnv)
visitModule env (Module mident imports decls)
   = let (isTDecl, isFDecl)
	             | genInterface env = (isPublicTypeDecl env, 
					   isPublicFuncDecl env)
		     | otherwise        = (isTypeDecl, isFuncDecl)
         (ts, env1)  = emap visitTypeDecl env  (filter isTDecl decls)
	 (fs, env2)  = emap visitFuncDecl env1 (filter isFDecl decls)
	 idecls      | genInterface env = getExportedIDecls env
		     | otherwise        = []
	 (ts', env3) = emap visitTypeIDecl env2 (filter isTypeIDecl idecls)
	 (fs', env4) = emap visitFuncIDecl env3 (filter isFuncIDecl idecls)
	 (os', env5) = emap visitOpIDecl   env4 (filter isOpIDecl   idecls)
	 prog        = Prog (visitModuleIdent mident)
		            (map visitModuleIdent imports)
			    (ts' ++ (genTypeSynonyms env5) ++ ts)
			    (fs' ++ fs)
			    (os' ++ (genOpDecls env5))
     in  (prog, env5)


--
visitTypeDecl :: FlatEnv -> Decl -> (TypeDecl, FlatEnv)
visitTypeDecl env (DataDecl qident arity cdecls)
   = let (cs, env1) = emap visitConstrDecl env cdecls
         typedecl   = Type (visitQualIdent env1 qident)
		           (getVisibility env1 qident)
			   [0 .. (arity - 1)]
			   cs
     in  (typedecl, env1)


--
visitConstrDecl :: FlatEnv -> ConstrDecl [Type] -> (ConsDecl, FlatEnv)
visitConstrDecl env (ConstrDecl qident tparams)
   = let (ts, env1) = emap visitType env tparams
	 consdecl   = Cons (visitQualIdent env1 qident)
		           (length tparams)
			   (getVisibility env1 qident)
			   ts
     in  (consdecl, env1)


--
visitType :: FlatEnv -> Type -> (TypeExpr, FlatEnv)
visitType env (TypeConstructor qident targs)
   = let (ts, env1) = emap visitType env targs
     in  if (qualName qident) == "Identity"
	     then (head ts, env1)
	     else (TCons (visitQualIdent env1 qident) ts, env1)
visitType env (TypeVariable index)
   = (TVar (int2num index), env)
visitType env (TypeArrow type1 type2)
   = let (t1, env1) = visitType env  type1
	 (t2, env2) = visitType env1 type2
     in  (FuncType t1 t2, env2)


--
visitVarIdent :: FlatEnv -> Ident -> (Int, FlatEnv)
visitVarIdent env ident
   = let vis  = varIds env
	 nidx | null vis  = 0
	      | otherwise = 1 + snd (head vis)
     in  maybe (nidx, env{ varIds = ((ident, nidx):vis) })
	       (\idx -> (idx, env))
	       (lookup ident vis)


--
visitFuncDecl :: FlatEnv -> Decl -> (FuncDecl, FlatEnv)
visitFuncDecl env (FunctionDecl qident params typeexpr expr)
   | genInterface env
     = let (ftypeexpr, env1) = visitType env typeexpr
       in  (Func (visitQualIdent env1 qident)
	         (length params)
	         Public
	         ftypeexpr
	         (Rule [] (Var 0)),
	    env1{ varIds = [] })
   | otherwise
     = let (fparams, env1)   = emap visitVarIdent env params
           (ftypeexpr, env2) = visitType env1 typeexpr
	   (fexpr, env3)     = visitExpression env2 expr
       in  (Func (visitQualIdent env3 qident)
	         (length params)
	         (getVisibility env3 qident)
	         ftypeexpr
	         (Rule fparams fexpr),
	    env3{ varIds = [] })

visitFuncDecl env (ExternalDecl qident _ name typeexpr)
   = let (ftypeexpr, env1) = visitType env typeexpr
	 funcdecl = Func (visitQualIdent env1 qident)
		         (getTypeArity typeexpr)
			 (getVisibility env1 qident)
			 ftypeexpr
			 (External (visitExternalName env name))
     in  (funcdecl, env1)

visitFuncDecl env (NewtypeDecl _ _ _)
   = error ("in module \"" 
	    ++ moduleName (moduleId env)
	    ++ "\" - newtype declarations are not supported")


--
visitExpression :: FlatEnv -> Expression -> (FlatCurry.Expr, FlatEnv)
visitExpression env (Literal lit)
   = let (flit, env1) = visitLiteral env lit
     in  (Lit flit, env1)

visitExpression env (Variable ident)
   = let (findex, env1) = visitVarIdent env ident
     in  (Var findex, env)

visitExpression env (Function qident _)
   = maybe (internalError (funcArity qident))
           (\arity -> genFuncCall env qident arity [])
	   (getArity env qident)
   -- | arity > 0 = (Comb (FuncPartCall arity) (visitQualIdent env qident) [], env)
   -- | otherwise = (Comb FuncCall (visitQualIdent env qident) [], env)

visitExpression env (Constructor qident arity)
   = maybe (internalError (consArity qident))
           (\arity -> genConsCall env qident arity [])
	   (getArity env qident)
   -- | arity > 0 = (Comb (ConsPartCall arity) (visitQualIdent env qident) [], env)
   -- | otherwise = (Comb ConsCall (visitQualIdent env qident) [], env)

visitExpression env (Apply expr1 expr2)
   = genFlatApplication env (Apply expr1 expr2)

visitExpression env (Case evalannot expr alts)
   = let (feval, env1) = visitEval env evalannot
	 (fexpr, env2) = visitExpression env1 expr
	 (falts, env3) = emap visitAlt env alts
     in  (FlatCurry.Case feval fexpr falts, env3)

visitExpression env (Or expr1 expr2)
   = let (fexpr1, env1) = visitExpression env  expr1
	 (fexpr2, env2) = visitExpression env1 expr2
     in  (FlatCurry.Or fexpr1 fexpr2, env2)

visitExpression env (Exist ident expr)
   = let (findex, env1) = visitVarIdent env ident
	 (fexpr, env2)  = visitExpression env1 expr
     in  case fexpr of
           Free findices' fexpr' -> (Free (findex:findices') fexpr', env2)
           _                     -> (Free [findex] fexpr, env2)

visitExpression env (Let binding expr)
   = let (fbinding, env1) = visitBinding env binding
	 (fexpr, env2)    = visitExpression env1 expr
     in  (FlatCurry.Let [fbinding] fexpr, env2)

visitExpression env (Letrec bindings expr)
   = let (fbindings, env1) = emap visitBinding env bindings
	 (fexpr, env2)     = visitExpression env1 expr
     in  (FlatCurry.Let fbindings fexpr, env2)


--
visitLiteral :: FlatEnv -> Literal -> (FlatCurry.Literal, FlatEnv)
visitLiteral env (Char c)  = (Charc c,  env)
visitLiteral env (Int i)   = (Intc i,   env)
visitLiteral env (Float f) = (Floatc f, env)


--
visitAlt :: FlatEnv -> Alt -> (BranchExpr, FlatEnv)
visitAlt env (Alt cterm expr)
   = let (fpatt, env1) = visitConstrTerm env cterm
         (fexpr, env2) = visitExpression env1 expr
     in  (Branch fpatt fexpr, env2)


--
visitConstrTerm :: FlatEnv -> ConstrTerm -> (Pattern, FlatEnv)
visitConstrTerm env (LiteralPattern lit)
   = let (flit, env1) = visitLiteral env lit
     in  (LPattern flit, env1)

visitConstrTerm env (ConstructorPattern qident args)
   = let (fargs, env1) = emap visitVarIdent env args
     in  (Pattern (visitQualIdent env qident) fargs, env1)

visitConstrTerm env (VariablePattern ident)
   = error ("in module \"" 
	    ++ moduleName (moduleId env)
	    ++ "\" - variable patterns are not supported")


--
visitEval :: FlatEnv -> Eval -> (FlatCurry.CaseType, FlatEnv)
visitEval env Rigid = (FlatCurry.Rigid, env)
visitEval env Flex  = (FlatCurry.Flex, env)


--
visitBinding :: FlatEnv -> Binding -> ((VarIndex, FlatCurry.Expr), FlatEnv)
visitBinding env (Binding ident expr)
   = let ids  = varIds env
	 env1 | isJust (lookup ident ids)
		= env{ varIds = filter (((/=) ident).fst) ids }
	      | otherwise
		= env
	 (findex, env2) = visitVarIdent env1 ident
	 (fexpr, env3)  = visitExpression env2 expr
     in  ((findex,fexpr), env3)


-------------------------------------------------------------------------------

--
visitFuncIDecl :: FlatEnv -> CurrySyntax.IDecl -> (FuncDecl, FlatEnv)
visitFuncIDecl env (CurrySyntax.IFunctionDecl _ qident arity typeexpr)
   = let (iltype, _)       = csType2ilType [] typeexpr
	 (ftypeexpr, env1) = visitType env iltype
         ffuncdecl         = Func (visitQualIdent env1 qident)
			          arity
				  Public
				  ftypeexpr
				  (External (qualName qident))
     in  (ffuncdecl, env1)


--
visitTypeIDecl :: FlatEnv -> CurrySyntax.IDecl -> (TypeDecl, FlatEnv)
visitTypeIDecl env (CurrySyntax.IDataDecl _ qident params mcdecls)
   = let fparams         = [0 .. ((length params) - 1)]
	 env1            = env{ tvarIds = zip params fparams }
	 cdecls          = map fromJust (filter isJust mcdecls)
	 (mmident, _)    = splitQualIdent qident
	 mident          = fromMaybe (error "IL2FlatCurry.visitTypeIDecl")
			             mmident
	 (fcdecls, env2) = emap (visitConstrIDecl mident) env1 cdecls
	 ftypedecl       = Type (visitQualIdent env2 qident)
			        Public
				fparams
				fcdecls
     in  (ftypedecl, env2)

visitTypeIDecl env (CurrySyntax.ITypeDecl _ qident params typeexpr)
   = let fparams           = [0 .. ((length params) - 1)]
	 tvis              = zip params fparams
	 (iltype, _)       = csType2ilType tvis typeexpr
	 (ftypeexpr, env1) = visitType env iltype
	 ftypedecl         = TypeSyn (visitQualIdent env1 qident)
			             Public
				     fparams
				     ftypeexpr
     in  (ftypedecl, env1)


--
visitConstrIDecl :: ModuleIdent -> FlatEnv -> CurrySyntax.ConstrDecl
		    -> (ConsDecl, FlatEnv)
visitConstrIDecl mident env (CurrySyntax.ConstrDecl _ _ ident typeexprs)
   = let qident             = qualifyWith mident ident
	 (iltypes, _)       = emap csType2ilType (tvarIds env) typeexprs
	 (ftypeexprs, env1) = emap visitType env iltypes
	 fconsdecl          = Cons (visitQualIdent env1 qident)
			           (length typeexprs)
				   Public
				   ftypeexprs
     in  (fconsdecl, env1)

visitConstrIDecl mident env (CurrySyntax.ConOpDecl _ _ type1 ident type2)
   = let qident = qualifyWith mident ident
	 (iltypes, _)       = emap csType2ilType (tvarIds env) [type1, type2]
	 (ftypeexprs, env1) = emap visitType env iltypes
	 fconsdecl          = Cons (visitQualIdent env1 qident)
			           2
				   Public
				   ftypeexprs
     in  (fconsdecl, env1)


--
visitOpIDecl :: FlatEnv -> CurrySyntax.IDecl -> (OpDecl, FlatEnv)
visitOpIDecl env (CurrySyntax.IInfixDecl _ fix prec qident)
   = let ffix | fix == CurrySyntax.InfixL = InfixlOp
	      | fix == CurrySyntax.InfixR = InfixrOp
	      | otherwise                 = InfixOp
         fopdecl = Op (visitQualIdent env qident) ffix prec
     in (fopdecl, env)


-------------------------------------------------------------------------------

--
visitModuleIdent :: ModuleIdent -> String
visitModuleIdent mident = moduleName mident


--
visitQualIdent :: FlatEnv -> QualIdent -> QName
visitQualIdent env qident = (mod, id)
 where
   mident        = moduleId env
   (mmod, ident) = splitQualIdent qident
   mod           | elem ident [listId, consId, nilId, unitId] 
		   || isTupleId ident
		   = moduleName preludeMIdent
		 | otherwise
		   = maybe (moduleName mident) moduleName mmod
   id            = name ident


--
visitExternalName :: FlatEnv -> String -> String
visitExternalName env name = (moduleName (moduleId env)) ++ "." ++ name


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
getVisibility :: FlatEnv -> QualIdent -> Visibility
getVisibility env qident
   | elem qident (getPublicIds info) = Public
   | otherwise                       = Private
 where
 info = curryInfo env


--
getExportedIDecls :: FlatEnv -> [CurrySyntax.IDecl]
getExportedIDecls env 
   = let mident     = moduleId env
	 menv       = moduleEnv env
	 info       = curryInfo env
	 exps       = getExports info
	 expImports = getExportedImports mident emptyEnv exps
     in  insertExportedIDecls menv [] (envToList expImports)


--
getExportedImports :: ModuleIdent -> Env ModuleIdent [Export] 
		      -> [Export] -> Env ModuleIdent [Export]
getExportedImports mident expenv [] = expenv
getExportedImports mident expenv ((Export qident):exps)
   = getExportedImports mident 
	         	(bindExportedImport mident qident (Export qident) expenv) 
			exps
getExportedImports mident expenv ((ExportTypeWith qident idents):exps)
   = getExportedImports mident 
		        (bindExportedImport mident 
		                            qident 
		                            (ExportTypeWith qident idents) 
		                            expenv)
			exps
getExportedImports mident expenv ((ExportTypeAll qident):exps)
   = getExportedImports mident 
	 	        (bindExportedImport mident qident (ExportTypeAll qident) expenv) 
			exps
getExportedImports mident expenv ((ExportModule mident'):exps)
   = getExportedImports mident (bindEnv mident' [] expenv) exps


--
bindExportedImport :: ModuleIdent -> QualIdent -> Export -> Env ModuleIdent [Export]
		       -> Env ModuleIdent [Export]
bindExportedImport mident qident export expenv
   | isJust (localIdent mident qident)
     = expenv
   | otherwise
     = let (mmod, _) = splitQualIdent qident
	   mod       = fromJust mmod
       in  maybe (bindEnv mod [export] expenv)
	         (\es -> bindEnv mod (export:es) expenv) 
		 (lookupEnv mod expenv)


--
insertExportedIDecls :: ModuleEnv -> [CurrySyntax.IDecl] -> [(ModuleIdent,[Export])]
			-> [CurrySyntax.IDecl]
insertExportedIDecls menv idecls [] = idecls
insertExportedIDecls menv idecls ((mident, exports):mes)
   = let idecls' = maybe idecls
		         (p_insertExportedIDecls mident idecls exports)
			 (lookupEnv mident menv)
     in insertExportedIDecls menv idecls' mes
 where
   p_insertExportedIDecls mident idecls exports impidecls
      | null exports = (map (qualifyIDecl mident) impidecls) ++ idecls
      | otherwise    = (filter (isExportedIDecl exports) 
			       (map (qualifyIDecl mident) impidecls))
		       ++ idecls


-- 
isExportedIDecl :: [Export] -> CurrySyntax.IDecl -> Bool
isExportedIDecl exports (CurrySyntax.IInfixDecl _ _ _ qident)
   = isExportedQualIdent qident exports
isExportedIDecl exports (CurrySyntax.IDataDecl _ qident _ _)
   = isExportedQualIdent qident exports
isExportedIDecl exports (CurrySyntax.ITypeDecl _ qident _ _)
   = isExportedQualIdent qident exports
isExportedIDecl exports (CurrySyntax.IFunctionDecl _ qident _ _)
   = isExportedQualIdent qident exports
isExportedIDecl exports _
   = False


--
isExportedQualIdent :: QualIdent -> [Export] -> Bool
isExportedQualIdent qident [] = False
isExportedQualIdent qident ((Export qident'):exps)
   = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((ExportTypeWith qident' idents):exps)
   = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((ExportTypeAll qident'):exps)
   = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((ExportModule _):exps)
   = isExportedQualIdent qident exps


--
qualifyIDecl :: ModuleIdent -> CurrySyntax.IDecl -> CurrySyntax.IDecl
qualifyIDecl mident (CurrySyntax.IInfixDecl pos fix prec qident)
   = (CurrySyntax.IInfixDecl pos fix prec (qualQualify mident qident))
qualifyIDecl mident (CurrySyntax.IDataDecl pos qident idents cdecls)
   = (CurrySyntax.IDataDecl pos (qualQualify mident qident) idents cdecls)
qualifyIDecl mident (CurrySyntax.INewtypeDecl pos qident idents ncdecl)
   = (CurrySyntax.INewtypeDecl pos (qualQualify mident qident) idents ncdecl)
qualifyIDecl mident (CurrySyntax.ITypeDecl pos qident idents texpr)
   = (CurrySyntax.ITypeDecl pos (qualQualify mident qident) idents texpr)
qualifyIDecl mident (CurrySyntax.IFunctionDecl pos qident arity texpr)
   = (CurrySyntax.IFunctionDecl pos (qualQualify mident qident) arity texpr)
qualifyIDecl _ idecl = idecl


--
getTypeArity :: Type -> Int
getTypeArity (TypeArrow _ t)       = 1 + (getTypeArity t)
getTypeArity (TypeConstructor _ _) = 0
getTypeArity (TypeVariable _)      = 0


--
genFlatApplication :: FlatEnv -> Expression -> (FlatCurry.Expr, FlatEnv)
genFlatApplication env applicexpr
   = genFlatApplic env [] applicexpr
 where
   genFlatApplic env args expr 
      = case expr of
	  (Apply expr1 expr2)    
	      -> genFlatApplic env (expr2:args) expr1
	  (Function qident _)
	      -> maybe (internalError (funcArity qident))
		       (\arity -> genFuncCall env qident arity args)
		       (getArity env qident)
	     -- -> case (qualLookupArity qident (arityEnv env)) of
		--   [ArityInfo qident' arity']
		--      -> p_genFuncCall env qident' arity' cnt args
		--   [] -> case (lookupArity (unqualify qident) (arityEnv env)) of
		--	   [ArityInfo qident' arity']
		--	      -> p_genFuncCall env qident' arity' cnt args
		--	   _  -> internalError (funcArity qident)
		--   _  ->  internalError (funcArity qident)
	  (Constructor qident _)
	      -> maybe (internalError (consArity qident))
		       (\arity -> genConsCall env qident arity args)
		       (getArity env qident)
	     -- -> case (qualLookupArity qident (arityEnv env)) of
		--   [ArityInfo qident' arity']
		--      -> p_genConsCall env qident' arity' cnt args
		--   [] -> case (lookupArity (unqualify qident) (arityEnv env)) of
		--	   [ArityInfo qident' arity']
		--	      -> p_genFuncCall env qident' arity' cnt args
		--	   _  -> internalError (consArity qident)
		--   _  -> internalError (consArity qident)
	  _   -> let (fexpr, env1) = visitExpression env expr
		 in  genApplicComb env fexpr args

   --p_genFuncCall env qident arity cnt args
   --   | arity > cnt = p_genComb env qident args (FuncPartCall (arity - cnt))
   --   | arity < cnt 
	-- = let (funcargs, applicargs) = splitAt arity args
	--      (funccall,env1)        = p_genComb env qident funcargs FuncCall 
	--  in  p_genApplicComb env1 funccall applicargs
   --   | otherwise   = p_genComb env qident args FuncCall 

   --p_genConsCall env qident arity cnt args
   --   | arity > cnt = p_genComb env qident args (ConsPartCall (arity - cnt))
   --   | arity < cnt 
	-- = let (funcargs, applicargs) = splitAt arity args
	--      (funccall,env1)        = p_genComb env qident funcargs ConsCall 
	--  in  p_genApplicComb env1 funccall applicargs
      -- | otherwise = p_genComb env qident args ConsCall 

   --p_genComb env qident args combtype 
   --   = let (fexpr, env1) = emap visitExpression env args
   --     in  (Comb combtype (visitQualIdent env1 qident) fexpr, env1)
	 
   --p_genApplicComb env fexpr [] = (fexpr, env)
   --p_genApplicComb env fexpr (e1:es)
   --   = let (fe1, env1) = visitExpression env e1
   --         appcomb     = Comb FuncCall 
	--		       (visitQualIdent env1 p_qidApply)
	--		       [fexpr, fe1]
	--in  p_genApplicComb env1 appcomb es

   --p_qidApply = qualifyWith preludeMIdent (mkIdent "apply")

   --funcArity qid = "cannot compute function arity of \"" ++ show qid ++ "\""
   --consArity qid = "cannot compute constructor arity of \"" ++ show qid ++ "\""

--
genFuncCall :: FlatEnv -> QualIdent -> Int -> [Expression]
	       -> (FlatCurry.Expr, FlatEnv)
genFuncCall env qident arity args
   | arity > cnt = genComb env qident args (FuncPartCall (arity - cnt))
   | arity < cnt 
     = let (funcargs, applicargs) = splitAt arity args
	   (funccall,env1)        = genComb env qident funcargs FuncCall 
       in  genApplicComb env1 funccall applicargs
   | otherwise   = genComb env qident args FuncCall
 where cnt = length args

--
genConsCall :: FlatEnv -> QualIdent -> Int -> [Expression]
	       -> (FlatCurry.Expr, FlatEnv)
genConsCall env qident arity args
   | arity > cnt = genComb env qident args (ConsPartCall (arity - cnt))
   | arity < cnt 
     = let (funcargs, applicargs) = splitAt arity args
	   (funccall,env1)        = genComb env qident funcargs ConsCall 
       in  genApplicComb env1 funccall applicargs
   | otherwise = genComb env qident args ConsCall 
 where cnt = length args

--
genComb :: FlatEnv -> QualIdent -> [Expression] -> FlatCurry.CombType
	   -> (FlatCurry.Expr, FlatEnv)
genComb env qident args combtype 
   = let (fexpr, env1) = emap visitExpression env args
     in  (Comb combtype (visitQualIdent env1 qident) fexpr, env1)
	 
--
genApplicComb :: FlatEnv -> FlatCurry.Expr -> [Expression]
		 -> (FlatCurry.Expr, FlatEnv)
genApplicComb env fexpr [] = (fexpr, env)
genApplicComb env fexpr (e1:es)
   = let (fe1, env1) = visitExpression env e1
	 appcomb     = Comb FuncCall 
		            (visitQualIdent env1 qidApply)
			    [fexpr, fe1]
     in  genApplicComb env1 appcomb es
 where
 qidApply = qualifyWith preludeMIdent (mkIdent "apply")

--
funcArity qid = "cannot compute function arity of \"" ++ show qid ++ "\""
consArity qid = "cannot compute constructor arity of \"" ++ show qid ++ "\""


--
genOpDecls :: FlatEnv -> [OpDecl]
genOpDecls env = map (genOpDecl env) (getOpFixity (curryInfo env))

--
genOpDecl :: FlatEnv -> CurrySyntax.IDecl -> OpDecl
genOpDecl env (CurrySyntax.IInfixDecl _ fixity prec qident)
   = Op (visitQualIdent env qident) (p_genOpFixity fixity) prec
 where
   p_genOpFixity CurrySyntax.InfixL = InfixlOp
   p_genOpFixity CurrySyntax.InfixR = InfixrOp
   p_genOpFixity CurrySyntax.Infix  = InfixOp


--
genTypeSynonyms :: FlatEnv -> [TypeDecl]
genTypeSynonyms env = map (genTypeSynonym env) (getTypeSyns (curryInfo env))

--
genTypeSynonym :: FlatEnv -> CurrySyntax.IDecl -> TypeDecl
genTypeSynonym env (CurrySyntax.ITypeDecl _ qident params typeexpr)
   = let fparams     = [0 .. ((length params) - 1)]
         (iltype, _) = csType2ilType (zip params fparams) typeexpr
	 (ftype, _)  = visitType env iltype
     in  TypeSyn (visitQualIdent env qident)
                 (getVisibility env qident)
		 fparams
		 ftype


--
csType2ilType :: [(Ident,Int)] -> CurrySyntax.TypeExpr -> (Type, [(Ident,Int)])
csType2ilType ids (CurrySyntax.ConstructorType qident typeexprs)
   = let (ilTypeexprs, ids') = emap csType2ilType ids typeexprs
     in  (TypeConstructor qident ilTypeexprs, ids')
csType2ilType ids (CurrySyntax.VariableType ident)
   = let mid        = lookup ident ids
	 nid        | null ids  = 0
		    | otherwise = 1 + snd (head ids)
	 (id, ids') | isJust mid = (fromJust mid, ids)
		    | otherwise  = (nid, (ident, nid):ids)
     in  (TypeVariable id, ids')
csType2ilType ids (CurrySyntax.ArrowType type1 type2)
   = let (ilType1, ids')  = csType2ilType ids type1
	 (ilType2, ids'') = csType2ilType ids' type2
     in  (TypeArrow ilType1 ilType2, ids'')
csType2ilType ids (CurrySyntax.ListType typeexpr)
   = let (ilTypeexpr, ids') = csType2ilType ids typeexpr
     in  (TypeConstructor (qualify listId) [ilTypeexpr], ids')
csType2ilType ids (CurrySyntax.TupleType typeexprs)
   | null typeexprs
     = (TypeConstructor qUnitId [], ids)
   | otherwise
     = let (ilTypeexprs, ids') = emap csType2ilType ids typeexprs
       in  (TypeConstructor (qTupleId ((length ilTypeexprs) - 1)) ilTypeexprs,
            ids')


-- Returns the arity (= number of parameters) of an indentifier
getArity :: FlatEnv -> QualIdent -> Maybe Int
getArity env qident
   = case (qualLookupArity qident aEnv) of
       [ArityInfo _ arity] -> Just arity
       []                  -> case (lookupArity (unqualify qident) aEnv) of
			        [ArityInfo _ arity] -> Just arity
				_                   -> Nothing
       _                   -> Nothing
 where aEnv = arityEnv env


-------------------------------------------------------------------------------

prelude_types :: [TypeDecl]
prelude_types = [(Type ("prelude","()") Public [] 
		  [(Cons ("prelude","()") 0 Public [])]),
		 (Type ("prelude","[]") Public [0] 
		  [(Cons ("prelude","[]") 0 Public []),
		   (Cons ("prelude",":") 2 Public 
		    [(TVar 0),(TCons ("prelude","[]") [(TVar 0)])])]),
		 (Type ("prelude","(,)") Public [0,1] 
		  [(Cons ("prelude","(,)") 2 Public [(TVar 0),(TVar 1)])]),
		 (Type ("prelude","(,,)") Public [0,1,2]
		  [(Cons ("prelude","(,,)") 3 Public 
		    [(TVar 0),(TVar 1),(TVar 2)])]),
		 (Type ("prelude","(,,,)") Public [0,1,2,3] 
		  [(Cons ("prelude","(,,,)") 4 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3)])]),
		 (Type ("prelude","(,,,,)") Public [0,1,2,3,4] 
		  [(Cons ("prelude","(,,,,)") 5 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),(TVar 4)])]),
		 (Type ("prelude","(,,,,,)") Public [0,1,2,3,4,5] 
		  [(Cons ("prelude","(,,,,,)") 6 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),(TVar 4),(TVar 5)])]),
		 (Type ("prelude","(,,,,,,)") Public [0,1,2,3,4,5,6] 
		  [(Cons ("prelude","(,,,,,,)") 7 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6)])]),
		 (Type ("prelude","(,,,,,,,)") Public [0,1,2,3,4,5,6,7] 
		  [(Cons ("prelude","(,,,,,,,)") 8 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7)])]),
		 (Type ("prelude","(,,,,,,,,)") Public [0,1,2,3,4,5,6,7,8] 
		  [(Cons ("prelude","(,,,,,,,,)") 9 Public
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8)])]),
		 (Type ("prelude","(,,,,,,,,,)") Public [0,1,2,3,4,5,6,7,8,9] 
		  [(Cons ("prelude","(,,,,,,,,,)") 10 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),(TVar 9)])]),
		 (Type ("prelude","(,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10] 
		  [(Cons ("prelude","(,,,,,,,,,,)") 11 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),
		     (TVar 9),(TVar 10)])]),
		 (Type ("prelude","(,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11] 
		  [(Cons ("prelude","(,,,,,,,,,,,)") 12 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),
		     (TVar 9),(TVar 10),(TVar 11)])]),
		 (Type ("prelude","(,,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11,12] 
		  [(Cons ("prelude","(,,,,,,,,,,,,)") 13 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),
		     (TVar 8),(TVar 9),(TVar 10),(TVar 11),(TVar 12)])]),
		 (Type ("prelude","(,,,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11,12,13] 
		  [(Cons ("prelude","(,,,,,,,,,,,,,)") 14 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),
		     (TVar 8),(TVar 9),(TVar 10),(TVar 11),
		     (TVar 12),(TVar 13)])]),
		 (Type ("prelude","(,,,,,,,,,,,,,,)") Public 
		  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] 
		  [(Cons ("prelude","(,,,,,,,,,,,,,,)") 15 Public 
		    [(TVar 0),(TVar 1),(TVar 2),(TVar 3),
		     (TVar 4),(TVar 5),(TVar 6),(TVar 7),
		     (TVar 8),(TVar 9),(TVar 10),(TVar 11),
		     (TVar 12),(TVar 13),(TVar 14)])])]


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
isTypeDecl :: Decl -> Bool
isTypeDecl (DataDecl _ _ _) = True
isTypeDecl _                = False

--
isFuncDecl :: Decl -> Bool
isFuncDecl (FunctionDecl _ _ _ _) = True
isFuncDecl (ExternalDecl _ _ _ _) = True
isFuncDecl _                      = False

--
isPublicTypeDecl :: FlatEnv -> Decl -> Bool
isPublicTypeDecl env (DataDecl qident _ _ )
   = (getVisibility env qident) == Public
isPublicTypeDecl env _ 
   = False

--
isPublicFuncDecl :: FlatEnv -> Decl -> Bool
isPublicFuncDecl env (FunctionDecl qident _ _ _)
   = (getVisibility env qident) == Public
isPublicFuncDecl env (ExternalDecl qident _ _ _)
   = (getVisibility env qident) == Public
isPublicFuncDecl env _ 
   = False


--
isTypeIDecl :: CurrySyntax.IDecl -> Bool
isTypeIDecl (CurrySyntax.IDataDecl _ _ _ _) = True
isTypeIDecl (CurrySyntax.ITypeDecl _ _ _ _) = True
isTypeIDecl _                               = False

--
isFuncIDecl :: CurrySyntax.IDecl -> Bool
isFuncIDecl (CurrySyntax.IFunctionDecl _ _ _ _) = True
isFuncIDecl _                                   = False

--
isOpIDecl :: CurrySyntax.IDecl -> Bool
isOpIDecl (CurrySyntax.IInfixDecl _ _ _ _) = True
isOpIDecl _                                = False 


--
getModuleIdent :: Module -> ModuleIdent
getModuleIdent (Module mident _ _) = mident


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

-- Data type representing an environment which contains information needed
-- for generating FlatCurry code.
data FlatEnv = FlatEnv { moduleId     :: ModuleIdent,
			 moduleEnv    :: ModuleEnv,
			 arityEnv     :: ArityEnv,
			 curryInfo    :: CurryInfo,
			 varIds       :: [(Ident, Int)],
			 tvarIds      :: [(Ident, Int)],
			 genInterface :: Bool
		       } deriving Show

-- Initial environment for generating FlatCurry code
initFlatEnv :: FlatEnv
initFlatEnv = FlatEnv { moduleId     = mkMIdent [],
			moduleEnv    = emptyEnv,
			arityEnv     = emptyTopEnv,
			curryInfo    = emptyCurryInfo,
			varIds       = [],
			tvarIds      = [],
			genInterface = False
		      }

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

