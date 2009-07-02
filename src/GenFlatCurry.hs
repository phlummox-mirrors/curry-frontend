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

import Control.Monad.State
import Control.Monad
import Data.Maybe
import Data.List
import qualified Data.Map as Map

import Curry.Base.MessageMonad
import Curry.Base.Ident as Id

import Base (ArityEnv, ArityInfo(..), ModuleEnv,  
	     TCEnv, TypeInfo(..), ValueEnv, ValueInfo(..),
	     lookupValue, qualLookupTC,
	     qualLookupArity, lookupArity,  internalError)
import Curry.ExtendedFlat
import qualified IL.Type as IL
import qualified Curry.Syntax as CS
import CurryEnv (CurryEnv)
import qualified CurryEnv
import ScopeEnv (ScopeEnv)
import qualified ScopeEnv
import Types
import CurryCompilerOpts
-- import Message
import PatchPrelude


trace _ x = x

-------------------------------------------------------------------------------

-- transforms intermediate language code (IL) to FlatCurry code
genFlatCurry :: Options -> CurryEnv -> ModuleEnv -> ValueEnv -> TCEnv 
		-> ArityEnv -> IL.Module -> (Prog, [WarnMsg])
genFlatCurry opts cEnv mEnv tyEnv tcEnv aEnv mod
   = (patchPreludeFCY prog, messages)
 where (prog, messages) 
	   = run opts cEnv mEnv tyEnv tcEnv aEnv False (visitModule mod)


-- transforms intermediate language code (IL) to FlatCurry interfaces
genFlatInterface :: Options -> CurryEnv -> ModuleEnv -> ValueEnv -> TCEnv
		 -> ArityEnv -> IL.Module -> (Prog, [WarnMsg])
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
	                   (nub (imps ++ (map (\ (CS.IImportDecl _ mid) 
					       -> mid) imps')))
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
	                   (nub (imps ++ (map (\ (CS.IImportDecl _ mid) 
					       -> mid) imps')))
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
	vis    <- getVisibility False qident
	return (Type qname vis [0 .. (arity - 1)] (concat cdecls))
visitDataDecl _ = internalError "GenFlatCurry: no data declaration"

--
visitConstrDecl :: IL.ConstrDecl [IL.Type] -> FlatState [ConsDecl]
visitConstrDecl (IL.ConstrDecl qident types)
   = do texprs <- mapM visitType types
	qname  <- visitQualIdent qident
	vis    <- getVisibility True qident
        genFint <- genInterface
        if genFint && vis == Private 
          then return []
          else return [Cons qname (length types) vis texprs]

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
	   vis   <- getVisibility False qident
	   clearVarIndices
	   return (Func qname (length params) vis texpr (Rule is expr)))
       (do setFunctionId qident
	   texpr <- visitType typeexpr
	   qname <- visitQualIdent qident
	   clearVarIndices
	   return (Func qname (length params) Public texpr (Rule [] (Var $ mkIdx 0))))
visitFuncDecl (IL.ExternalDecl qident _ name typeexpr)
   = do setFunctionId qident
	texpr <- visitType typeexpr
	qname <- visitQualIdent qident
	vis   <- getVisibility False qident
	xname <- visitExternalName name
	return (Func qname (typeArity typeexpr) vis texpr (External xname))
visitFuncDecl (IL.NewtypeDecl _ _ _)
   = do mid <- moduleId 
	error ("\"" ++ Id.moduleName mid 
	       ++ "\": newtype declarations are not supported")
visitFuncDecl _ = internalError "GenFlatCurry: no function declaration"

--
visitExpression :: IL.Expression -> FlatState Expr
visitExpression (IL.Literal literal)
   = liftM Lit (visitLiteral literal)
visitExpression (IL.Variable ident)
   = liftM Var (lookupVarIndex ident)
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
visitExpression (IL.Case r evalannot expression alts)
   = do ea       <- visitEval evalannot
	expr     <- visitExpression expression
	branches <- mapM visitAlt alts
	return (Case r ea expr branches)
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


getTypeOf :: Ident -> FlatState (Maybe TypeExpr)
getTypeOf ident = do
    (valEnv, _) <- environments
    case lookupValue ident valEnv of 
      Value _ (ForAll _ t) : _ 
          -> do t <- visitType (ttrans t)
                trace ("getTypeOf(" ++ show ident ++ ") = " ++ show t)$
                      return (Just t)
      v   -> trace ("lookupValue did not return a value for index " ++ show ident ++ ", instead " ++ show v)
             (return Nothing)
    where ttrans :: Type -> IL.Type 
          ttrans (TypeConstructor i ts)
              = IL.TypeConstructor i (map ttrans ts)
          ttrans (TypeVariable v)
              = IL.TypeVariable v
          ttrans (TypeConstrained [] v)
              = trace (msg1 v) $ IL.TypeVariable v
          ttrans (TypeConstrained (v:_) i)
              = trace (msg2 i ilt) ilt
              where ilt = ttrans v
          ttrans (TypeArrow f x) = IL.TypeArrow (ttrans f) (ttrans x)
          ttrans s@(TypeSkolem _) = error $ "in ttrans: " ++ show s
          ttrans s@(TypeRecord _ _) = error $ "in ttrans: " ++ show s
          msg1 i = "in ttrans: empty TypeConstrained, coerced to type var #" ++ show i
          msg2 i t = "in ttrans: TypeConstrained with index " ++ show i ++ ", coerced to " ++ show t

--
visitLiteral :: IL.Literal -> FlatState Literal
visitLiteral (IL.Char rs c)  = return (Charc rs c)
visitLiteral (IL.Int rs i)   = return (Intc rs i)
visitLiteral (IL.Float rs f) = return (Floatc rs f)

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
	error ("\"" ++ Id.moduleName mid 
	       ++ "\": variable patterns are not supported")

--
visitEval :: IL.Eval -> FlatState CaseType
visitEval IL.Rigid = return (Rigid)
visitEval IL.Flex  = return (Flex)

--
visitBinding :: IL.Binding -> FlatState (VarIndex, Expr)
visitBinding (IL.Binding ident expression)
   = do index <- lookupVarIndex ident
	expr  <- visitExpression expression
	return (index, expr)


-------------------------------------------------------------------------------

--
visitFuncIDecl :: CS.IDecl -> FlatState FuncDecl
visitFuncIDecl (CS.IFunctionDecl _ qident arity typeexpr)
   = do texpr <- visitType (fst (cs2ilType [] typeexpr))
	qname <- visitQualIdent qident
	return (Func qname arity Public texpr (Rule [] (Var $ mkIdx 0)))
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
visitModuleIdent mident = return (Id.moduleName mident)

--
visitQualIdent :: QualIdent -> FlatState QName
visitQualIdent qident
   = do mid <- moduleId
	let (mmod, ident) = splitQualIdent qident
	    mod | elem ident [listId, consId, nilId, unitId] || isTupleId ident
		  = Id.moduleName preludeMIdent
		| otherwise
		  = maybe (Id.moduleName mid) Id.moduleName mmod
	return (curry mkQName mod $ name ident)

--
visitExternalName :: String -> FlatState String
visitExternalName name 
   = moduleId >>= (\mid -> return ((Id.moduleName mid) ++ "." ++ name))


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
getVisibility :: Bool -> QualIdent -> FlatState Visibility
getVisibility isConstr qident
   = do public <- isPublic isConstr qident
	if public then return Public else return Private


--
getExportedImports :: FlatState [CS.IDecl]
getExportedImports
   = do mid  <- moduleId
	exps <- exports
	genExportedIDecls (Map.toList (getExpImports mid Map.empty exps))

--
getExpImports :: ModuleIdent -> Map.Map ModuleIdent [CS.Export] -> [CS.Export]
		 -> Map.Map ModuleIdent [CS.Export]
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
   = getExpImports mident (Map.insert mident' [] expenv) exps

--
bindExpImport :: ModuleIdent -> QualIdent -> CS.Export 
	         -> Map.Map ModuleIdent [CS.Export] -> Map.Map ModuleIdent [CS.Export]
bindExpImport mident qident export expenv
   | isJust (localIdent mident qident)
     = expenv
   | otherwise
     = let (mmod, _) = splitQualIdent qident
	   mod       = fromJust mmod
       in  maybe (Map.insert mod [export] expenv)
	         (\es -> Map.insert mod (export:es) expenv) 
		 (Map.lookup mod expenv)

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


-- The intermediate language (IL) does not represent type synonyms
-- (and also no record declarations). For this reason an interface
-- representation of all type synonyms is generated (see "CurryEnv")
-- from the abstract syntax representation of the Curry program.
-- The function 'typeSynonyms' returns this list of type synonyms.
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
	vis   <- getVisibility False qident
	return (TypeSyn qname vis is texpr)
genTypeSynonym _ = internalError "GenFlatCurry: no type synonym interface"


-- In order to provide an interface for record declarations, 'genRecordTypes'
-- generates dummy data declarations representing records together
-- with their typed labels. For the record declaration
--
--      type Rec = {l_1 :: t_1,..., l_n :: t_n}
--
-- the following data declaration will be generated:
--
--      data Rec' = l_1' t_1 | ... | l_n' :: t_n
--
-- Rec' and l_i' are unique idenfifiers which encode the original names
-- Rec and l_i.
-- When reading an interface file containing such declarations, it is
-- now possible to reconstruct the original record declaration. Since
-- usual FlatCurry code is used, these declaration should not have any
-- effects on the behaviour of the Curry program. But to ensure correctness,
-- these dummies should be generated for the interface file as well as for
-- the corresponding FlatCurry file.
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

-- FlatCurry provides no possibility of representing record types like
-- {l_1::t_1, l_2::t_2, ..., l_n::t_n}. So they have to be transformed to
-- to the corresponding type constructors which are defined in the record 
-- declarations. 
-- Unlike data declarations or function type annotations, type synonyms and
-- record declarations are not generated from the intermediate language.
-- So the transformation has only to be performed in these cases.
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
	         let ms = foldl (matchTypeVars fs) Map.empty fs'
		     types = map (\i -> maybe 
			 	          (CS.VariableType 
					     (mkIdent ("#tvar" ++ show i)))
				          (elimRecordTypes tyEnv tcEnv)
				          (Map.lookup i ms))
			         [0 .. n-1]
	         in  CS.ConstructorType record types
	       _ -> internalError ("GenFlatCurry.elimRecordTypes: "
		 		   ++ "no record type")
	   _ -> internalError ("GenFlatCurry.elimRecordTypes: "
			       ++ "no label")

matchTypeVars :: [(Ident,CS.TypeExpr)] -> Map.Map Int CS.TypeExpr
	      -> (Ident, Type) -> Map.Map Int CS.TypeExpr
matchTypeVars fs ms (l,ty)
   = maybe ms (match ms ty) (lookup l fs)
  where
  match ms (TypeVariable i) typeexpr = Map.insert i typeexpr ms
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
 checkOverlap (Case _ _ _ _) _ 
    = do qid <- functionId
	 genWarning (overlappingRules qid)
 checkOverlap _ (Case _ _ _ _)
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
   = case typeexprs of
       []  -> (IL.TypeConstructor qUnitId [], ids)
       [t] -> cs2ilType ids t
       _   -> let (ilTypeexprs, ids') = emap cs2ilType ids typeexprs
		  tuplen = length ilTypeexprs
	      in  (IL.TypeConstructor (qTupleId tuplen) ilTypeexprs,
		   ids')
cs2ilType _ typeexpr = internalError ("cs2ilType: " ++ show typeexpr)


-------------------------------------------------------------------------------
-- Messages for internal errors and warnings

funcArity qid = "GenFlatCurry: missing arity for function \"" 
		++ show qid ++ "\""

consArity qid = "GenFlatCurry: missing arity for constructor \""
		++ show qid ++ "\""

missingVarIndex id = "GenFlatCurry: missing index for \"" ++ show id ++ "\""


overlappingRules qid =  "function \""
		        ++ show qid 
		        ++ "\" is non-deterministic due to non-trivial "
		        ++ "overlapping rules"


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
isPublicDataDecl (IL.DataDecl qident _ _ ) = isPublic False qident
isPublicDataDecl _                         = return False

--
isPublicFuncDecl :: IL.Decl -> FlatState Bool
isPublicFuncDecl (IL.FunctionDecl qident _ _ _) = isPublic False qident
isPublicFuncDecl (IL.ExternalDecl qident _ _ _) = isPublic False qident
isPublicFuncDecl _                              = return False

--
isTypeIDecl :: CS.IDecl -> Bool
isTypeIDecl (CS.IDataDecl _ _ _ _) = True
isTypeIDecl (CS.ITypeDecl _ _ _ _) = True
isTypeIDecl _                      = False

--
isRecordIDecl :: CS.IDecl -> Bool
isRecordIDecl (CS.ITypeDecl _ _ _ (CS.RecordType (_:_) _)) = True
isRecordIDecl _                                            = False

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
int2num = abs


emap :: (e -> a -> (b,e)) -> e -> [a] -> ([b], e)
emap _ env []     = ([], env)
emap f env (x:xs) = let (x',env')    = f env x
			(xs', env'') = emap f env' xs
		    in  ((x':xs'), env'')

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for representing an environment which contains information needed
-- for generating FlatCurry code.
data FlatEnv = FlatEnv{ moduleIdE     :: ModuleIdent,
			  functionIdE   :: QualIdent,
			  compilerOptsE :: Options,
			  moduleEnvE    :: ModuleEnv,
			  arityEnvE     :: ArityEnv,
			  typeEnvE      :: ValueEnv,
			  tConsEnvE     :: TCEnv,
			  publicEnvE    :: Map.Map Ident IdentExport,
			  fixitiesE     :: [CS.IDecl],
			  typeSynonymsE :: [CS.IDecl],
			  importsE      :: [CS.IDecl],
			  exportsE      :: [CS.Export],
			  interfaceE    :: [CS.IDecl],
			  varIndexE     :: Int,
			  varIdsE       :: ScopeEnv Ident VarIndex,
			  tvarIndexE    :: Int,
			  tvarIdsE      :: ScopeEnv Ident TVarIndex,
			  messagesE     :: [WarnMsg],
			  genInterfaceE :: Bool
			}

data IdentExport = NotConstr       -- function, type-constructor
                 | OnlyConstr      -- constructor
                 | NotOnlyConstr   -- constructor, function, type-constructor



-- The environment 'FlatEnv' is embedded in the monadic representation
-- 'FlatState' which allows the usage of 'do' expressions.
type FlatState a = State FlatEnv a


-- Runs a 'FlatState' action and returns the result
run :: Options -> CurryEnv -> ModuleEnv -> ValueEnv -> TCEnv -> ArityEnv 
    -> Bool -> FlatState a -> (a, [WarnMsg])
run opts cEnv mEnv tyEnv tcEnv aEnv genIntf f
   = (result, messagesE env)
 where
 (result, env) = runState f env0
 env0 = FlatEnv{ moduleIdE     = CurryEnv.moduleId cEnv,
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
		 genInterfaceE = genIntf
	       }


--
moduleId :: FlatState ModuleIdent
moduleId = gets moduleIdE

--
functionId :: FlatState QualIdent
functionId = gets functionIdE

--
setFunctionId :: QualIdent -> FlatState ()
setFunctionId qid = modify (\env -> env{ functionIdE = qid })

--
compilerOpts :: FlatState Options
compilerOpts = gets compilerOptsE

--
exports :: FlatState [CS.Export]
exports = gets exportsE

--
imports :: FlatState [CS.IDecl]
imports = gets importsE

--
records :: FlatState [CS.IDecl]
records = gets (filter isRecordIDecl . interfaceE)

--
fixities :: FlatState [CS.IDecl]
fixities = gets fixitiesE

--
typeSynonyms :: FlatState [CS.IDecl]
typeSynonyms = gets typeSynonymsE

--
environments :: FlatState (ValueEnv,TCEnv)
environments = gets (\env -> (typeEnvE env, tConsEnvE env))

--
isPublic :: Bool -> QualIdent -> FlatState Bool
isPublic isConstr qid = gets (\env -> maybe False isP
                                      (Map.lookup (unqualify qid) 
                                       (publicEnvE env)))
  where
    isP NotConstr = not isConstr
    isP OnlyConstr = isConstr
    isP NotOnlyConstr = True

--
lookupModuleIntf :: ModuleIdent -> FlatState (Maybe [CS.IDecl])
lookupModuleIntf mid
   = gets (Map.lookup mid . moduleEnvE)

--
lookupIdArity :: QualIdent -> FlatState (Maybe Int)
lookupIdArity qid
   = gets (lookupA qid . arityEnvE)
 where
 lookupA qid aEnv = case (qualLookupArity qid aEnv) of
		      [ArityInfo _ a]
		         -> Just a
		      [] -> case (lookupArity (unqualify qid) aEnv) of
			      [ArityInfo _ a] -> Just a
			      _               -> Nothing
		      _  -> Nothing

-- Generates a new index for a variable
newVarIndex :: Ident -> FlatState VarIndex
newVarIndex id
   = do idx0 <- gets varIndexE
        ty <- getTypeOf id
        let idx = idx0 + 1
            vid = VarIndex ty idx
        vids <- gets varIdsE
        modify (\env -> env{ varIndexE = idx,
			     varIdsE   = ScopeEnv.insert id vid vids
			   })
        return vid

--
lookupVarIndex :: Ident -> FlatState VarIndex
lookupVarIndex id
   = do index_ <- gets (ScopeEnv.lookup id . varIdsE)
        maybe (internalError (missingVarIndex id)) return index_

--
clearVarIndices :: FlatState ()
clearVarIndices = modify (\env -> env { varIndexE = 0,
				        varIdsE = ScopeEnv.new 
				      })

--
genWarning :: String -> FlatState ()
genWarning msg
   = modify (\env -> env{ messagesE = warnMsg:(messagesE env) })
    where warnMsg = WarnMsg Nothing msg

--
genInterface :: FlatState Bool
genInterface = gets genInterfaceE

--
beginScope :: FlatState ()
beginScope = modify
	       (\env -> env { varIdsE  = ScopeEnv.beginScope (varIdsE env),
			      tvarIdsE = ScopeEnv.beginScope (tvarIdsE env)
			    })

--
endScope :: FlatState ()
endScope = modify
	     (\env -> env { varIdsE  = ScopeEnv.endScope (varIdsE env),
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
genPubEnv :: ModuleIdent -> [CS.IDecl] -> Map.Map Ident IdentExport
genPubEnv mid idecls = foldl (bindEnvIDecl mid) Map.empty idecls

bindIdentExport :: Ident -> Bool -> Map.Map Ident IdentExport -> Map.Map Ident IdentExport
bindIdentExport id isConstr env =
    maybe (Map.insert id (if isConstr then OnlyConstr else NotConstr) env)
          (\ ie -> Map.insert id (updateIdentExport ie isConstr) env)
          (Map.lookup id env)
  where
    updateIdentExport OnlyConstr True  = OnlyConstr
    updateIdentExport OnlyConstr False = NotOnlyConstr
    updateIdentExport NotConstr True   = NotOnlyConstr
    updateIdentExport NotConstr False  = NotConstr
    updateIdentExport NotOnlyConstr _  = NotOnlyConstr


--
bindEnvIDecl :: ModuleIdent -> Map.Map Ident IdentExport -> CS.IDecl -> Map.Map Ident IdentExport
bindEnvIDecl mid env (CS.IDataDecl _ qid _ mcdecls)
   = maybe env 
           (\id -> foldl bindEnvConstrDecl
	                 (bindIdentExport id False env)
	                 (catMaybes mcdecls))
	   (localIdent mid qid)
bindEnvIDecl mid env (CS.INewtypeDecl _ qid _ ncdecl)
   = maybe env 
           (\id -> bindEnvNewConstrDecl (bindIdentExport id False env) ncdecl)
	   (localIdent mid qid)
bindEnvIDecl mid env (CS.ITypeDecl _ qid _ texpr)
   = maybe env (\id -> bindEnvITypeDecl env id texpr) (localIdent mid qid)
bindEnvIDecl mid env (CS.IFunctionDecl _ qid _ _)
   = maybe env (\id -> bindIdentExport id False env) (localIdent mid qid)
bindEnvIDecl _ env _ = env

--
bindEnvITypeDecl :: Map.Map Ident IdentExport -> Ident -> CS.TypeExpr
		    -> Map.Map Ident IdentExport
bindEnvITypeDecl env id (CS.RecordType fs _)
   = bindIdentExport id False (foldl (bindEnvRecordLabel id) env fs)
bindEnvITypeDecl env id texpr
   = bindIdentExport id False env

--
bindEnvConstrDecl :: Map.Map Ident IdentExport -> CS.ConstrDecl -> Map.Map Ident IdentExport
bindEnvConstrDecl env (CS.ConstrDecl _ _ id _)  = bindIdentExport id True env
bindEnvConstrDecl env (CS.ConOpDecl _ _ _ id _) = bindIdentExport id True env

--
bindEnvNewConstrDecl :: Map.Map Ident IdentExport -> CS.NewConstrDecl -> Map.Map Ident IdentExport
bindEnvNewConstrDecl env (CS.NewConstrDecl _ _ id _) = bindIdentExport id False env

--
bindEnvRecordLabel :: Ident -> Map.Map Ident IdentExport -> ([Ident],CS.TypeExpr) 
		   -> Map.Map Ident IdentExport
bindEnvRecordLabel rec env ([lab],_)
   = bindIdentExport (recSelectorId (qualify rec) lab)
             False
	     (bindIdentExport (recUpdateId (qualify rec) lab) False env)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
