module IL2FlatCurry where

import IL
import Ident
import Env
import CurryInfo
import FlatCurry hiding (Literal, Expr(Or, Case, Let), CaseType(..))
import qualified FlatCurry (Literal, Expr(Or, Case, Let), CaseType(..))
import qualified CurrySyntax
import Maybe


-------------------------------------------------------------------------------

-- transforms intermediate language code (IL) to FlatCurry code
il2flatCurry :: CurryInfo -> Module -> Prog
il2flatCurry info (Module mident imports decls) 
   = fst (visitModule env (Module mident imports decls))
 where
 env = flatEnv mident info


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
visitModule :: FlatEnv -> Module -> (Prog, FlatEnv)
visitModule env (Module mident imports decls)
   = let (ts, env2) = mapVisit visitTypeDecl env  (filter isTypeDecl decls)
	 (fs, env3) = mapVisit visitFuncDecl env2 (filter isFuncDecl decls)
	 prog       = Prog (visitModuleIdent mident)
		           (map visitModuleIdent imports)
			   ts
			   fs
			   (genOpDecls env3)
     in  (prog, env3)


--
visitTypeDecl :: FlatEnv -> Decl -> (TypeDecl, FlatEnv)
visitTypeDecl env (DataDecl qident arity cdecls)
   = let (cs, env1) = mapVisit visitConstrDecl env cdecls
         typedecl   = Type (visitQualIdent env1 qident)
		           (getVisibility env1 qident)
			   [0 .. (arity - 1)]
			   cs
     in  (typedecl, env1)


--
visitConstrDecl :: FlatEnv -> ConstrDecl [Type] -> (ConsDecl, FlatEnv)
visitConstrDecl env (ConstrDecl qident tparams)
   = let (ts, env1) = mapVisit visitType env tparams
	 consdecl   = Cons (visitQualIdent env1 qident)
		           (length tparams)
			   (getVisibility env1 qident)
			   ts
     in  (consdecl, env1)


--
visitType :: FlatEnv -> Type -> (TypeExpr, FlatEnv)
visitType env (TypeConstructor qident targs)
   = let (ts, env1) = mapVisit visitType env targs
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
   | isJust idx = (fromJust idx, env)
   | otherwise  = (idx', env')
 where
 vis  = varIds env
 idx  = lookup ident vis
 idx' = 1 + (if null vis then 0 else snd (head vis))
 env' = env{ varIds = ((ident, idx'):vis) }


--
visitFuncDecl :: FlatEnv -> Decl -> (FuncDecl, FlatEnv)
visitFuncDecl env (FunctionDecl qident params typeexpr expr)
   = let (fparams, env1)   = mapVisit visitVarIdent env params
         (ftypeexpr, env2) = visitType env1 typeexpr
	 (fexpr, env3)     = visitExpression env2 expr
         funcdecl          = Func (visitQualIdent env2 qident)
		                  (length params)
				  (getVisibility env3 qident)
				  ftypeexpr
				  (Rule fparams fexpr)
     in  (funcdecl, (env3{ varIds = [] }))

visitFuncDecl env (ExternalDecl qident _ name typeexpr)
   = let (ftypeexpr, env1) = visitType env typeexpr
	 funcdecl          = Func (visitQualIdent env1 qident)
			          (getArityFromType typeexpr)
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

visitExpression env (Function qident arity)
   | arity > 0 = (Comb (PartCall arity) (visitQualIdent env qident) [], env)
   | otherwise = (Comb FuncCall (visitQualIdent env qident) [], env)

visitExpression env (Constructor qident _)
   = (Comb ConsCall (visitQualIdent env qident) [], env)

visitExpression env (Apply expr1 expr2)
   = genFlatApplication env (Apply expr1 expr2)

visitExpression env (Case evalannot expr alts)
   = let (feval, env1) = visitEval env evalannot
	 (fexpr, env2) = visitExpression env1 expr
	 (falts, env3) = mapVisit visitAlt env alts
     in  (FlatCurry.Case feval fexpr falts, env3)

visitExpression env (Or expr1 expr2)
   = let (fexpr1, env1) = visitExpression env  expr1
	 (fexpr2, env2) = visitExpression env1 expr2
     in  (FlatCurry.Or fexpr1 fexpr2, env2)

visitExpression env (Exist ident expr)
   = let (fexpr, env1)  = visitExpression env expr
	 (findex, env2) = visitVarIdent env1 ident
     in  (Free [findex] fexpr, env1)

visitExpression env (Let binding expr)
   = let (fbinding, env1) = visitBinding env binding
	 (fexpr, env2)    = visitExpression env1 expr
     in  (FlatCurry.Let [fbinding] fexpr, env2)

visitExpression env (Letrec bindings expr)
   = let (fbindings, env1) = mapVisit visitBinding env bindings
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
   = let (fargs, env1) = mapVisit visitVarIdent env args
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
   = let (fexpr, env1)  = visitExpression env expr
	 (findex, env2) = visitVarIdent env1 ident
     in  ((findex,fexpr), env2)


--
mapVisit :: (FlatEnv -> a -> (b, FlatEnv)) -> FlatEnv -> [a] -> ([b], FlatEnv)
mapVisit visitTerm env [] = ([], env)
mapVisit visitTerm env (term:terms)
   = let (term', env')   = visitTerm env term
         (terms', env'') = mapVisit visitTerm env' terms
     in  ((term':terms'), env'')


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


------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--
getVisibility :: FlatEnv -> QualIdent -> Visibility
getVisibility env qident
   | elem (unqualify qident) (getExports info) = Public
   | otherwise                                    = Private
 where
 info = curryInfo env


--
getArityFromType :: Type -> Int
getArityFromType (TypeArrow _ t)       = 1 + (getArityFromType t)
getArityFromType (TypeConstructor _ _) = 0
getArityFromType (TypeVariable _)      = 0


--
genFlatApplication :: FlatEnv -> Expression -> (FlatCurry.Expr, FlatEnv)
genFlatApplication env applicexpr
   = p_genFlatApplic env 0 [] applicexpr
 where
   p_genFlatApplic env cnt args expr
      = case expr of
	  (Apply expr1 expr2)    
	      -> p_genFlatApplic env (cnt + 1) (expr2:args) expr1
	  (Function qident arity) 
	      -> p_genFuncCall env qident (arity - cnt) args
	  (Constructor qident _)  
	      -> p_genConsCall env qident args
	  _                       
	      -> let (fexpr, env1) = visitExpression env expr
		 in  p_genApplicComb env fexpr args

   p_genFuncCall env qident missing args
      | missing > 0 = p_genComb env qident args (PartCall missing)
      | otherwise   = p_genComb env qident args FuncCall

   p_genConsCall env qident args
      = p_genComb env qident args ConsCall

   p_genComb env qident args combtype
      = let (fexpr, env1) = mapVisit visitExpression env args
        in  (Comb combtype (visitQualIdent env qident) fexpr, env1)
	 
   p_genApplicComb env fexpr [] = (fexpr, env)
   p_genApplicComb env fexpr (e1:es)
      = let (fe1, env1) = visitExpression env e1
            appcomb     = Comb FuncCall 
			       (visitQualIdent env p_qidApply)
			       [fexpr, fe1]
	in  p_genApplicComb env1 appcomb es

   p_qidApply = qualifyWith preludeMIdent (mkIdent "apply")


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


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
isTypeDecl :: Decl -> Bool
isTypeDecl decl = case decl of
		    DataDecl _ _ _ -> True
		    _              -> False

--
isFuncDecl :: Decl -> Bool
isFuncDecl decl = case decl of
		    FunctionDecl _ _ _ _ -> True
		    NewtypeDecl _ _ _    -> True
		    ExternalDecl _ _ _ _ -> True
		    _                    -> False


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

int2num :: Int -> Int
int2num i | i < 0     = (-1) * i
	  | otherwise = i


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


data FlatEnv = FlatEnv { moduleId  :: ModuleIdent,
			 curryInfo :: CurryInfo,
			 varIds    :: [(Ident, Int)],
			 tvarIds   :: [(Ident, Int)]
		       }

--
flatEnv mid info = FlatEnv{ moduleId  = mid,
			    curryInfo = info,
			    varIds    = [],
			    tvarIds   = []
			  }

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

