module CaseCompletion where


import qualified CurrySyntax
import Base (ModuleEnv, lookupModule)
import IL
import Ident
import ScopeEnv
import ILScope
import Maybe


-------------------------------------------------------------------------------

-- Noetige Parameter:
-- mEnv - fuer importierte Konstruktoren
-- mod  - fuer Konstruktoren des gleichen Moduls

--
completeCase :: ModuleEnv -> Module -> Module
completeCase menv mod = let (mod', _) = visitModule menv mod in mod'


-------------------------------------------------------------------------------

--
visitModule :: ModuleEnv -> Module -> (Module, [Message])
visitModule menv (Module mident imports decls)
   = ((Module mident (insertUnique preludeMIdent imports) decls'), msgs')
 where
   (decls', msgs') = visitList (visitDecl (Module mident imports decls) menv)
		               insertDeclScope
			       []
			       (getModuleScope (Module mident imports decls))
			       decls


--
visitDecl :: Module -> ModuleEnv -> [Message] -> ScopeEnv -> Decl
	     -> (Decl, [Message])
visitDecl mod menv msgs senv (DataDecl qident arity cdecls)
   = ((DataDecl qident arity cdecls), msgs)

visitDecl mod menv msgs senv (NewtypeDecl qident arity cdecl)
   = ((NewtypeDecl qident arity cdecl), msgs)

visitDecl mod menv msgs senv (FunctionDecl qident params typeexpr expr)
   = ((FunctionDecl qident params typeexpr expr'), msgs)
 where
   (expr', msgs') = visitExpr mod menv msgs (insertExprScope senv expr) expr

visitDecl mod menv msgs senv (ExternalDecl qident cconv name typeexpr)
   = ((ExternalDecl qident cconv name typeexpr), msgs)


--
visitExpr :: Module -> ModuleEnv -> [Message] -> ScopeEnv -> Expression 
	     -> (Expression, [Message])
visitExpr mod menv msgs senv (Literal lit) 
   = ((Literal lit), msgs)

visitExpr mod menv msgs senv (Variable ident) 
   = ((Variable ident), msgs)

visitExpr mod menv msgs senv (Function qident arity) 
   = ((Function qident arity), msgs)

visitExpr mod menv msgs senv (Constructor qident arity)
   = ((Constructor qident arity), msgs)

visitExpr mod menv msgs senv (Apply expr1 expr2)
   = ((Apply expr1' expr2'), msgs2)
 where
   (expr1', msgs1) = visitExpr mod menv msgs (insertExprScope senv expr1) expr1
   (expr2', msgs2) = visitExpr mod menv msgs1 (insertExprScope senv expr2) expr2

visitExpr mod menv msgs senv (Case evalannot expr alts)
   | null altsR
     = intError "visitExpr" "empty alternative list"
   | isConstrAlt altR
     = (completeConsAlts mod menv senv evalannot expr' altsR, msgs3)
   | isLitAlt altR
     = (completeLitAlts evalannot expr' altsR, msgs3)
   | isVarAlt altR
     = (completeVarAlts expr' altsR, msgs3)
   | otherwise 
     = intError "visitExpr" "illegal alternative list"
 where
   altR           = head altsR
   (expr', msgs1) = visitExpr mod menv msgs (insertExprScope senv expr) expr
   (alts', msgs2) = visitList (visitAlt mod menv) insertAltScope msgs senv alts
   (altsR, msgs3) = removeRedundantAlts msgs alts'

visitExpr mod menv msgs senv (Or expr1 expr2)
   = ((Or expr1' expr2'), msgs2)
 where
   (expr1', msgs1) = visitExpr mod menv msgs (insertExprScope senv expr1) expr1
   (expr2', msgs2) = visitExpr mod menv msgs1 (insertExprScope senv expr2) expr2

visitExpr mod menv msgs senv (Exist ident expr)
   = ((Exist ident expr'), msgs')
 where
   (expr', msgs') = visitExpr mod menv msgs (insertExprScope senv expr) expr

visitExpr mod menv msgs senv (Let bind expr)
   = ((Let bind' expr'), msgs2)
 where
   (expr', msgs1) = visitExpr mod menv msgs (insertExprScope senv expr) expr
   (bind', msgs2) = visitBinding mod menv msgs (insertBindingScope senv bind) bind

visitExpr mod menv msgs senv (Letrec binds expr)
   = ((Letrec binds' expr'), msgs2)
 where
   (expr', msgs1)  = visitExpr mod menv msgs (insertExprScope senv expr) expr
   (binds', msgs2) = visitList (visitBinding mod menv)
		               const
			       msgs1
			       (foldl insertBindingScope senv binds)
			       binds


--
visitAlt :: Module -> ModuleEnv -> [Message] -> ScopeEnv -> Alt 
	    -> (Alt, [Message])
visitAlt mod menv msgs senv (Alt pattern expr)
   = ((Alt pattern expr'), msgs')
 where
   (expr', msgs') = visitExpr mod menv msgs (insertExprScope senv expr) expr


--
visitBinding :: Module -> ModuleEnv -> [Message] -> ScopeEnv -> Binding 
	        -> (Binding, [Message])
visitBinding mod menv msgs senv (Binding ident expr)
   = ((Binding ident expr'), msgs')
 where
   (expr', msgs') = visitExpr mod menv msgs (insertExprScope senv expr) expr


--
visitList :: ([Message] -> ScopeEnv -> a -> (a, [Message]))
	     -> (ScopeEnv -> a -> ScopeEnv)
	     -> [Message] -> ScopeEnv -> [a]
	     -> ([a], [Message])
visitList visitTerm insertScope msgs senv []
   = ([], msgs)
visitList visitTerm insertScope msgs senv (term:terms)
   = ((term':terms'), msgs2)
 where
   (term', msgs1)  = visitTerm msgs (insertScope senv term) term
   (terms', msgs2) = visitList visitTerm insertScope msgs1 senv terms

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
completeConsAlts :: Module -> ModuleEnv -> ScopeEnv 
		    -> Eval -> Expression -> [Alt]
		    -> Expression
completeConsAlts mod menv senv evalannot expr alts
   = (Case evalannot expr (alts1 ++ alts2))
 where
   defaultexpr = getDefaultExpr alts
   alts1       = filter isConstrAlt alts
   constrs     = (map p_getConsAltIdent alts1)
   cconsinfos  = getComplConstrs mod menv constrs
   cconstrs    = map (p_genConstrTerm senv) cconsinfos
   alts2       = map (\cconstr -> (Alt cconstr defaultexpr)) cconstrs

   p_getConsAltIdent (Alt (ConstructorPattern qident _) _) = qident

   p_genConstrTerm senv (qident, arity)
      = ConstructorPattern qident (ScopeEnv.genIdentList arity "x" senv)


--
completeLitAlts :: Eval -> Expression -> [Alt] -> Expression
completeLitAlts evalannot expr [] = failedExpr
completeLitAlts evalannot expr (alt:alts)
   | isLitAlt alt = (Case evalannot 
		          (eqExpr expr (p_makeLitExpr alt))
		          [(Alt truePatt  (getAltExpr alt)),
			   (Alt falsePatt (completeLitAlts evalannot expr alts))])
   | otherwise    = getAltExpr alt
 where
   p_makeLitExpr alt
      = case (getAltPatt alt) of
	  LiteralPattern lit -> Literal lit
	  _                  -> intError "completeLitAlts" 
				         "literal pattern expected"


--
completeVarAlts :: Expression -> [Alt] -> Expression
completeVarAlts expr [] = failedExpr
completeVarAlts expr (alt:_)
   = (Let (Binding (p_getVarIdent alt) expr) (getAltExpr alt))
 where
   p_getVarIdent alt
      = case (getAltPatt alt) of
	  VariablePattern ident -> ident
	  _                     -> intError "completeVarAlts" 
				            "variable pattern expected"


-------------------------------------------------------------------------------

-- Removes redundant case alternatives
removeRedundantAlts :: [Message] -> [Alt] -> ([Alt], [Message])
removeRedundantAlts msgs alts
   = let
         (alts1, msgs1) = removeIdleAlts msgs alts
	 (alts2, msgs2) = removeMultipleAlts msgs1 alts1
     in
         (alts2, msgs2)


-- Removes idle alternative (i.e. removes all alternatives
-- which occur behind the first alternative containing a variable pattern);
-- e.g. in
--    case x of
--      (y:ys) -> e1
--      z      -> e2
--      []     -> e3
-- all alternatives behind (z -> e2) will be removed (here: [] -> e3)
removeIdleAlts :: [Message] -> [Alt] -> ([Alt], [Message])
removeIdleAlts msgs alts 
   | null alts2 = (alts1, msgs)
   | otherwise  = (alts1, msgs)
 where
   (alts1, alts2) = splitAfter isVarAlt alts


-- Removes multiple occurances of alternatives; e.g. in
--    case x of
--      []     -> e1
--      (y:ys) -> e2
--      []     -> e3
-- the last alternative will be removed
removeMultipleAlts :: [Message] -> [Alt] -> ([Alt], [Message])
removeMultipleAlts msgs alts
   = p_remove msgs [] alts
 where
   p_remove msgs altsR []     = ((reverse altsR), msgs)
   p_remove msgs altsR (alt:alts)
      | p_containsAlt alt altsR = p_remove msgs altsR alts
      | otherwise               = p_remove msgs (alt:altsR) alts

   p_containsAlt alt alts = any (p_eqAlt alt) alts

   p_eqAlt (Alt (LiteralPattern lit1) _) alt2
      = case alt2 of
	  (Alt (LiteralPattern lit2) _) -> lit1 == lit2
	  _                             -> False
   p_eqAlt (Alt (ConstructorPattern qident1 _) _) alt2
      = case alt2 of
	  (Alt (ConstructorPattern qident2 _) _) -> qident1 == qident2
	  _                                      -> False
   p_eqAlt (Alt (VariablePattern _) _) alt2
      = case alt2 of
	  (Alt (VariablePattern _) _) -> True
	  _                           -> False


-------------------------------------------------------------------------------

--
isVarAlt :: Alt -> Bool
isVarAlt alt = case (getAltPatt alt) of
	         VariablePattern _ -> True
		 _                 -> False

--
isConstrAlt :: Alt -> Bool
isConstrAlt alt = case (getAltPatt alt) of
		    ConstructorPattern _ _ -> True
		    _                      -> False

--
isLitAlt :: Alt -> Bool
isLitAlt alt = case (getAltPatt alt) of
	         LiteralPattern _ -> True
		 _                -> False


--
getAltExpr :: Alt -> Expression
getAltExpr (Alt _ expr) = expr


--
getAltPatt :: Alt -> ConstrTerm
getAltPatt (Alt cterm _) = cterm


--
getDefaultExpr :: [Alt] -> Expression
getDefaultExpr alts 
   = maybe failedExpr getAltExpr (find isVarAlt alts)


-------------------------------------------------------------------------------

--
failedExpr :: Expression
failedExpr = Function (qualifyWith preludeMIdent (mkIdent "failed")) 0

--
eqExpr :: Expression -> Expression -> Expression
eqExpr e1 e2 = Apply
	         (Apply 
		   (Function (qualifyWith preludeMIdent (mkIdent "==")) 2)
		   e1)
		 e2


--
truePatt :: ConstrTerm
truePatt = ConstructorPattern qTrueId []

--
falsePatt :: ConstrTerm
falsePatt = ConstructorPattern qFalseId []



-------------------------------------------------------------------------------

--
getComplConstrs :: Module -> ModuleEnv -> [QualIdent] -> [(QualIdent, Int)]
getComplConstrs (Module mid _ decls) menv constrs
   | null constrs 
     = intError "getComplConstrs" "empty constructor list"
   | cons == qNilId || cons == qConsId
     = getCC constrs [(qNilId, 0), (qConsId, 2)]
   | mid' == mid
     = getCCFromDecls mid constrs decls
   | otherwise
     = maybe [] -- error ...
             (getCCFromIDecls mid' constrs) 
	     (lookupModule mid' menv)
 where
   cons = head constrs
   (mmid', _) = splitQualIdent cons
   mid' = maybe mid id mmid'


--
getCCFromDecls :: ModuleIdent -> [QualIdent] -> [Decl] -> [(QualIdent, Int)]
getCCFromDecls _ constrs decls
   = let
         cdecls = maybe [] -- error ...
		        p_extractConstrDecls
			(find (p_declaresConstr (head constrs)) decls)
	 cinfos = map p_getConstrDeclInfo cdecls
     in
         getCC constrs cinfos
 where
   p_declaresConstr qident decl
      = case decl of
	  DataDecl _ _ cdecls   -> any (p_isConstrDecl qident) cdecls
	  NewtypeDecl _ _ cdecl -> p_isConstrDecl qident cdecl
	  _                     -> False

   p_isConstrDecl qident (ConstrDecl qid _) = qident == qid

   p_extractConstrDecls decl
      = case decl of
	  DataDecl _ _ cdecls   -> cdecls
	  _                     -> []

   p_getConstrDeclInfo (ConstrDecl qident types) = (qident, length types)


--
getCCFromIDecls :: ModuleIdent -> [QualIdent] -> [CurrySyntax.IDecl] 
		   -> [(QualIdent, Int)]
getCCFromIDecls mident constrs idecls
   = let
         cdecls = maybe [] -- error ...
		        p_extractIConstrDecls
		        (find (p_declaresIConstr (head constrs)) idecls)
	 cinfos = map (p_getIConstrDeclInfo mident) cdecls
     in
         getCC constrs cinfos
 where
   p_declaresIConstr qident idecl
      = case idecl of
	  CurrySyntax.IDataDecl _ _ _ cdecls
	      -> any (p_isIConstrDecl qident) 
		     (map fromJust (filter isJust cdecls))
	  CurrySyntax.INewtypeDecl _ _ _ ncdecl 
	      -> p_isINewConstrDecl qident ncdecl
	  _   -> False

   p_isIConstrDecl qident (CurrySyntax.ConstrDecl _ _ ident _)
      = (unqualify qident) == ident
   p_isIConstrDecl qident (CurrySyntax.ConOpDecl _ _ _ ident _)
      = (unqualify qident) == ident

   p_isINewConstrDecl qident (CurrySyntax.NewConstrDecl _ _ ident _)
      = (unqualify qident) == ident

   p_extractIConstrDecls idecl
      = case idecl of
	  CurrySyntax.IDataDecl _ _ _ cdecls 
	      -> map fromJust (filter isJust cdecls)
	  _   -> []

   p_getIConstrDeclInfo mid (CurrySyntax.ConstrDecl _ _ ident types)
      = (qualifyWith mid ident, length types)
   p_getIConstrDeclInfo mid (CurrySyntax.ConOpDecl _ _ _ ident _)
      = (qualifyWith mid ident, 2)


--
getCC :: [QualIdent] -> [(QualIdent, Int)] -> [(QualIdent, Int)]
getCC _ [] = []
getCC constrs ((qident,arity):cis)
   | any ((==) qident) constrs = getCC constrs cis
   | otherwise                 = (qident,arity):(getCC constrs cis)


-------------------------------------------------------------------------------
-- Message handling
-- Not in use in this version, but intended for further versions

type Message = String


-------------------------------------------------------------------------------
-- Miscellaneous

--
splitAfter :: (a -> Bool) -> [a] -> ([a], [a])
splitAfter cond xs = p_splitAfter cond [] xs
 where
   p_splitAfter c fs []     = ((reverse fs),[])
   p_splitAfter c fs (l:ls) | c l       = ((reverse (l:fs)), ls)
			    | otherwise = p_splitAfter c (l:fs) ls


--
find :: (a -> Bool) -> [a] -> Maybe a
find _    []     = Nothing
find cond (x:xs) | cond x    = Just x
		 | otherwise = find cond xs


--
insertUnique :: Eq a => a -> [a] -> [a]
insertUnique x xs | elem x xs = xs
		  | otherwise = x:xs


--
intError :: String -> String -> a
intError fun msg = error ("CaseCompletion." ++ fun ++ " - " ++ msg)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------