-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- WarnCheck - Generates the following warning messages: ...
--                
-- November 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module WarnCheck (warnCheck) where

import CurrySyntax
import Ident
import Position
import Base (ValueEnv)
import TopEnv
import Message
import Env
import Monad


-------------------------------------------------------------------------------

warnCheck :: ValueEnv -> Module -> [Message CompMessageType]
warnCheck tyEnv (Module mid _ decls)
   = run (addImports tyEnv >> checkDecls mid decls)

-- Die Importdecls getrennt betrachten.

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- The following functions check a curry program (in 'CurrySyntax' 
-- representation) for unreferenced and shadowing variables as well as
-- idle and overlapping case alternatives.

checkDecls :: ModuleIdent -> [Decl] -> CheckState ()
checkDecls  mid decls
   = do foldM' insertDecl decls
	foldM' (checkDecl mid) decls

--
checkDecl :: ModuleIdent -> Decl -> CheckState ()
checkDecl mid (DataDecl pos ident params cdecls)
   = do visitTypeId ident
	beginScope
	foldM' insertTypeVar params
	foldM' (checkConstrDecl mid) cdecls
	params' <- filterM isUnrefTypeVar params
	when (not (null params')) 
	     (foldM' (genWarning pos) (map unrefTypeVar params'))
	endScope
checkDecl mid (TypeDecl pos ident params texpr)
   = do visitTypeId ident
	beginScope
	foldM' insertTypeVar params
	checkTypeExpr mid pos texpr
	params' <- filterM isUnrefTypeVar params
	when (not (null params'))
	     (foldM' (genWarning pos) (map unrefTypeVar params'))
	endScope
checkDecl mid (FunctionDecl pos ident equs)
   = do visitId ident
	beginScope
	foldM' (checkEquation mid) equs
	endScope
checkDecl mid (ExternalDecl _ _ _ ident _)
   = visitId ident
checkDecl mid (FlatExternalDecl _ idents)
   = foldM' visitId idents
checkDecl mid (PatternDecl pos cterm rhs)
   = do checkConstrTerm mid pos cterm
	insertConstrTerm cterm
	checkRhs mid rhs
checkDecl mid (ExtraVariables pos idents)
   = do idents' <- filterM isShadowingVar idents
	when (not (null idents'))
	     (foldM' (genWarning pos) (map shadowingVar idents'))
	foldM' insertVar idents
checkDecl _ _ = return ()

--
checkConstrDecl :: ModuleIdent -> ConstrDecl -> CheckState ()
checkConstrDecl mid (ConstrDecl pos _ ident texprs)
   = do visitTypeId ident
	foldM' (checkTypeExpr mid pos) texprs
checkConstrDecl mid (ConOpDecl pos _ texpr1 ident texpr2)
   = do visitTypeId ident
	checkTypeExpr mid pos texpr1
	checkTypeExpr mid pos texpr2

--
checkTypeExpr :: ModuleIdent -> Position -> TypeExpr -> CheckState ()
checkTypeExpr mid pos (ConstructorType _ texprs)
   = foldM' (checkTypeExpr mid pos) texprs
checkTypeExpr mid pos (VariableType ident)
   = visitTypeId ident
checkTypeExpr mid pos (TupleType texprs)
   = foldM' (checkTypeExpr mid pos) texprs
checkTypeExpr mid pos (ListType texpr)
   = checkTypeExpr mid pos texpr
checkTypeExpr mid pos (ArrowType texpr1 texpr2)
   = do checkTypeExpr mid pos texpr1
	checkTypeExpr mid pos texpr2

--
checkEquation :: ModuleIdent -> Equation -> CheckState ()
checkEquation mid (Equation pos lhs rhs)
   = do checkLhs mid pos lhs
	checkRhs mid rhs
	idents' <- returnUnrefVars
	when (not (null idents')) 
             (foldM' (genWarning pos) (map unrefVar idents'))

--
checkLhs :: ModuleIdent -> Position -> Lhs -> CheckState ()
checkLhs mid pos (FunLhs ident cterms)
   = do visitId ident
	foldM' (checkConstrTerm mid pos) cterms
	foldM' insertConstrTerm cterms
checkLhs mid pos (OpLhs cterm1 ident cterm2)
   = checkLhs mid pos (FunLhs ident [cterm1, cterm2])
checkLhs mid pos (ApLhs lhs cterms)
   = do checkLhs mid pos lhs
	foldM' (checkConstrTerm mid pos) cterms
	foldM' insertConstrTerm cterms

--
checkRhs :: ModuleIdent -> Rhs -> CheckState ()
checkRhs mid (SimpleRhs pos expr decls)
   = do foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	checkExpression mid pos expr
checkRhs mid (GuardedRhs cexprs decls)
   = do foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	foldM' (checkCondExpr mid) cexprs

--
checkCondExpr :: ModuleIdent -> CondExpr -> CheckState ()
checkCondExpr mid (CondExpr pos cond expr)
   = do checkExpression mid pos cond
	checkExpression mid pos expr

-- 
checkConstrTerm :: ModuleIdent -> Position -> ConstrTerm -> CheckState ()
checkConstrTerm mid pos (VariablePattern ident)
   = when' (isShadowingVar ident) (genWarning pos (shadowingVar ident))
checkConstrTerm mid pos (ConstructorPattern _ cterms)
   = foldM' (checkConstrTerm mid pos) cterms
checkConstrTerm mid pos (InfixPattern cterm1 qident cterm2)
   = checkConstrTerm mid pos (ConstructorPattern qident [cterm1, cterm2])
checkConstrTerm mid pos (ParenPattern cterm)
   = checkConstrTerm mid pos cterm
checkConstrTerm mid pos (TuplePattern cterms)
   = foldM' (checkConstrTerm mid pos) cterms
checkConstrTerm mid pos (ListPattern cterms)
   = foldM' (checkConstrTerm mid pos) cterms
checkConstrTerm mid pos (AsPattern ident cterm)
   = do when' (isShadowingVar ident) (genWarning pos (shadowingVar ident))
	checkConstrTerm mid pos cterm
checkConstrTerm mid pos (LazyPattern cterm)
   = checkConstrTerm mid pos cterm
checkConstrTerm _ _ _ = return ()

--
checkExpression :: ModuleIdent -> Position -> Expression -> CheckState ()
checkExpression mid pos (Variable qident)
   = maybe (return ()) visitId (localIdent mid qident)
checkExpression mid pos (Paren expr)
   = checkExpression mid pos expr
checkExpression mid pos (Typed expr _)
   = checkExpression mid pos expr
checkExpression mid pos (Tuple exprs)
   = foldM' (checkExpression mid pos) exprs
checkExpression mid pos (List exprs)
   = foldM' (checkExpression mid pos) exprs
checkExpression mid pos (ListCompr expr stmts)
   = do beginScope
	foldM' (checkStatement mid pos) stmts
	checkExpression mid pos expr
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkExpression mid pos (EnumFrom expr)
   = checkExpression mid pos expr
checkExpression mid pos (EnumFromThen expr1 expr2)
   = foldM' (checkExpression mid pos) [expr1, expr2]
checkExpression mid pos (EnumFromTo expr1 expr2)
   = foldM' (checkExpression mid pos) [expr1, expr2]
checkExpression mid pos (EnumFromThenTo expr1 expr2 expr3)
   = foldM' (checkExpression mid pos) [expr1, expr2, expr3]
checkExpression mid pos (UnaryMinus _ expr)
   = checkExpression mid pos expr
checkExpression mid pos (Apply expr1 expr2)
   = foldM' (checkExpression mid pos) [expr1, expr2]
checkExpression mid pos (InfixApply expr1 _ expr2)
   = foldM' (checkExpression mid pos) [expr1, expr2]
checkExpression mid pos (LeftSection expr _)
   = checkExpression mid pos expr
checkExpression mid pos (RightSection _ expr)
   = checkExpression mid pos expr
checkExpression mid pos (Lambda cterms expr)
   = do beginScope
	foldM' (checkConstrTerm mid pos) cterms
	foldM' insertConstrTerm cterms
	checkExpression mid pos expr
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkExpression mid pos (Let decls expr)
   = do beginScope
	foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	checkExpression mid pos expr
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkExpression mid pos (Do stmts expr)
   = do beginScope
	foldM' (checkStatement mid pos) stmts
	checkExpression mid pos expr
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkExpression mid pos (IfThenElse expr1 expr2 expr3)
   = foldM' (checkExpression mid pos) [expr1, expr2, expr3]
checkExpression mid pos (Case expr alts)
   = do checkExpression mid pos expr
	beginScope
	foldM' (checkAlt mid) alts
	idents' <-  returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	checkCaseAlternatives mid alts
	endScope
checkExpression _ _ _ = return ()

--
checkStatement :: ModuleIdent -> Position -> Statement -> CheckState ()
checkStatement mid pos (StmtExpr expr)
   = checkExpression mid pos expr
checkStatement mid pos (StmtDecl decls)
   = do foldM' insertDecl decls
	foldM' (checkDecl mid) decls
checkStatement mid pos (StmtBind cterm expr)
   = do checkConstrTerm mid pos cterm
	insertConstrTerm cterm
	checkExpression mid pos expr

--
checkAlt :: ModuleIdent -> Alt -> CheckState ()
checkAlt mid (Alt pos cterm rhs)
   = do checkConstrTerm mid pos cterm
	insertConstrTerm cterm
	checkRhs mid rhs

-- Check for idle and overlapping case alternatives
checkCaseAlternatives :: ModuleIdent -> [Alt] -> CheckState ()
checkCaseAlternatives mid alts
   = do checkIdleAlts mid alts
	checkOverlappingAlts mid alts

--
checkIdleAlts :: ModuleIdent -> [Alt] -> CheckState ()
checkIdleAlts mid alts
   = do alts' <- dropUnless' isVarAlt alts
	let idles = tail_ alts'
	    (Alt pos _ _) = head idles
	unless (null idles) (genWarning pos idleCaseAlts)
 where
 isVarAlt (Alt _ (VariablePattern id) _) 
    = isVarId id
 isVarAlt (Alt _ (ParenPattern (VariablePattern id)) _) 
    = isVarId id
 isVarAlt (Alt _ (AsPattern _ (VariablePattern id)) _)
    = isVarId id
 isVarAlt _ = return False

--
checkOverlappingAlts :: ModuleIdent -> [Alt] -> CheckState ()
checkOverlappingAlts mid [] = return ()
checkOverlappingAlts mid (alt:alts)
   = do (altsr, alts') <- partition' (equalAlts alt) alts
        mapM_ (\ (Alt pos _ _) -> genWarning pos overlappingCaseAlt) altsr
	checkOverlappingAlts mid alts'
 where
 equalAlts (Alt _ cterm1 _) (Alt _ cterm2 _) = equalConstrTerms cterm1 cterm2

 equalConstrTerms (LiteralPattern l1) (LiteralPattern l2)
    = return (l1 == l2)
 equalConstrTerms (NegativePattern id1 l1) (NegativePattern id2 l2) 
    = return (id1 == id2 && l1 == l2)
 equalConstrTerms (VariablePattern id1) (VariablePattern id2)
    = do p <- isDeclId id1 
	 return (p && id1 == id2)
 equalConstrTerms (ConstructorPattern qid1 cs1)
		  (ConstructorPattern qid2 cs2)
    = if qid1 == qid2
      then all' (\ (c1,c2) -> equalConstrTerms c1 c2) (zip cs1 cs2)
      else return False
 equalConstrTerms (InfixPattern lcs1 qid1 rcs1)
		  (InfixPattern lcs2 qid2 rcs2)
    = equalConstrTerms (ConstructorPattern qid1 [lcs1, rcs1])
                       (ConstructorPattern qid2 [lcs2, rcs2])
 equalConstrTerms (ParenPattern cterm1) (ParenPattern cterm2)
    = equalConstrTerms cterm1 cterm2
 equalConstrTerms (TuplePattern cs1) (TuplePattern cs2)
    = equalConstrTerms (ConstructorPattern (qTupleId 2) cs1)
                       (ConstructorPattern (qTupleId 2) cs2)
 equalConstrTerms (ListPattern cs1) (ListPattern cs2)
    = equalConstrTerms (ConstructorPattern qListId cs1)
                       (ConstructorPattern qListId cs2)
 equalConstrTerms (AsPattern id1 cterm1) (AsPattern id2 cterm2)
    = equalConstrTerms cterm1 cterm2
 equalConstrTerms (LazyPattern cterm1) (LazyPattern cterm2)
    = equalConstrTerms cterm1 cterm2
 equalConstrTerms _ _ = return False


-------------------------------------------------------------------------------
-- The following actions updates the current state by adding identifiers
-- occuring in declaration left hand sides

--
insertDecl :: Decl -> CheckState ()
insertDecl (DataDecl _ ident _ cdecls)
   = do insertTypeDeclId ident
	foldM' insertConstrDecl cdecls
insertDecl (TypeDecl _ ident _ _)
   = insertTypeDeclId ident
insertDecl (FunctionDecl _ ident _)
   = insertVar ident
insertDecl (ExternalDecl _ _ _ ident _)
   = insertVar ident
insertDecl (FlatExternalDecl _ idents)
   = foldM' insertVar idents
 --insertDecl (PatternDecl _ cterm _)
 --   = insertConstrTerm cterm
 --insertDecl (ExtraVariables _ idents)
 --   = foldM' insertId idents
insertDecl _ = return ()

--
insertConstrDecl :: ConstrDecl -> CheckState ()
insertConstrDecl (ConstrDecl _ _ ident _)
   = insertDeclId ident
insertConstrDecl (ConOpDecl _ _ _ ident _)
   = insertDeclId ident

--
insertConstrTerm :: ConstrTerm -> CheckState ()
insertConstrTerm (VariablePattern ident)
   = unless' (isDeclId ident) (insertVar ident)
insertConstrTerm (ConstructorPattern _ cterms)
   = foldM' insertConstrTerm cterms
insertConstrTerm (InfixPattern cterm1 qident cterm2)
   = insertConstrTerm (ConstructorPattern qident [cterm1, cterm2])
insertConstrTerm (ParenPattern cterm)
   = insertConstrTerm cterm
insertConstrTerm (TuplePattern cterms)
   = foldM' insertConstrTerm cterms
insertConstrTerm (ListPattern cterms)
   = foldM' insertConstrTerm cterms
insertConstrTerm (AsPattern ident cterm)
   = do insertVar ident
	insertConstrTerm cterm
insertConstrTerm (LazyPattern cterm)
   = insertConstrTerm cterm
insertConstrTerm _ = return ()


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for distinguishing identifiers either as common declarations
-- (i.e. functions, constructors or type constructors) or (type) variables.
-- To mark all variables which are used within expressions the corresponding
-- constructor has a Boolean flag. 
-- T O D O !!!!!!!!!!!!!!!!!
data IdInfo = DeclInfo | VarInfo Bool

--
isVariable :: IdInfo -> Bool
isVariable (VarInfo _) = True
isVariable _           = False

--
isDeclaration :: IdInfo -> Bool
isDeclaration DeclInfo = True
isDeclaration _        = False

--
variableVisited :: IdInfo -> Bool
variableVisited (VarInfo v) = v
variableVisited _           = True

--
visitVariable :: IdInfo -> IdInfo
visitVariable info = case info of
		       VarInfo _ -> VarInfo True
		       _         -> info


-- Data type for representing the current state of generating warnings.
-- It contains a list of generated messages and an environment holding
-- information of identifiers of the current scope.
-- The monadic representation of the state allows the usage of monadic 
-- operators. which makes it easier and safer to deal with the contents.
data CheckState a 
   = CheckState ([Message CompMessageType] -> ScopeEnv QualIdent IdInfo
		 -> ([Message CompMessageType], 
		     ScopeEnv QualIdent IdInfo, 
		     a))

-- 'CheckState' is declared as an instance of 'Monad' to use its actions
-- in 'do' expressions
instance Monad CheckState where

 -- (>>=) :: CheckState a -> (a -> CheckState b) -> CheckState b
 (CheckState f) >>= g 
    = CheckState (\msgs senv -> let (msgs',senv',val') = f msgs senv
		                    CheckState h       = g val'
		                in  h msgs' senv')

 -- (>>) :: CheckState a -> CheckState b -> CheckState b
 a >> b = a >>= (\_ -> b)

 -- return :: a -> CheckState a
 return val = CheckState (\msgs senv -> (msgs,senv,val))



--
genWarning :: Position -> String -> CheckState ()
genWarning pos msg
   = CheckState (\msgs senv 
		 -> ((message (Warning pos) msg):msgs,
		     senv,
		     ()))

--
insertVar :: Ident -> CheckState ()
insertVar id 
   | isAnnonId id = return ()
   | otherwise    
     = CheckState (\msgs senv
		   -> (msgs,
		       insertSE (commonId id) (VarInfo False) senv,
		       ()))

--
insertTypeVar :: Ident -> CheckState ()
insertTypeVar id
   | isAnnonId id = return ()
   | otherwise    
     = CheckState (\msgs senv
		   -> (msgs,
		       insertSE (typeId id) (VarInfo False) senv,
		       ()))

--
insertDeclId :: Ident -> CheckState ()
insertDeclId id
   | isAnnonId id = return ()
   | otherwise    
     = CheckState (\msgs senv
		   -> (msgs,
		       insertSE (commonId id) DeclInfo senv,
		       ()))

--
insertTypeDeclId :: Ident -> CheckState ()
insertTypeDeclId id
   | isAnnonId id = return ()
   | otherwise    
     = CheckState (\msgs senv
		   -> (msgs,
		       insertSE (typeId id) DeclInfo senv,
		       ()))

--
insertQualId :: QualIdent -> CheckState ()
insertQualId qid
   = CheckState (\msgs senv
		 -> (msgs,
		     insertSE qid DeclInfo senv,
		     ()))

--
isVarId :: Ident -> CheckState Bool
isVarId id = CheckState (\msgs senv
			  -> (msgs,
			      senv,
			      maybe (isAnnonId id) 
			            isVariable 
			            (lookupSE (commonId id) senv)))
--
isDeclId :: Ident -> CheckState Bool
isDeclId id = CheckState (\msgs senv
			  -> (msgs,
			      senv,
			      maybe False 
			            isDeclaration 
			            (lookupSE (commonId id) senv)))

-- Sinnvoller waere hier eine Funktion, die nicht nur auf Existenz prueft,
-- sondern gleichzeiting auch noch die Level vergleicht.
--existsId :: Ident -> CheckState Bool
--existsId id = CheckState (\msgs senv
--			  -> (msgs,
--			      senv,
--			      existsSE (unRenameIdent id) senv))

--
isShadowingVar :: Ident -> CheckState Bool
isShadowingVar id 
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     (maybe False isVariable (lookupSE id' senv)
		      && levelSE id' senv < currentLevelSE senv)))
 where id' = commonId id

--
isShadowingTypeVar :: Ident -> CheckState Bool
isShadowingTypeVar id
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     (maybe False isVariable (lookupSE id' senv)
		      && levelSE id' senv < currentLevelSE senv)))
 where id' = typeId id

--
--existsTypeId :: Ident -> CheckState Bool
--existsTypeId id = CheckState (\msgs senv
--			      -> (msgs,
--				  senv,
--				  existsSE (renameIdent id 1) senv))

--
visitId :: Ident -> CheckState ()
visitId id = CheckState (\msgs senv
			 -> (msgs,
			     modifySE visitVariable (commonId id) senv,
			     ()))

--
visitTypeId :: Ident -> CheckState ()
visitTypeId id = CheckState (\msgs senv
			     -> (msgs,
				 modifySE visitVariable (typeId id) senv,
				 ()))

--
isUnrefVar :: Ident -> CheckState Bool
isUnrefVar id 
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     maybe True 
		           (not . variableVisited)
		           (lookupSE (commonId id) senv)))


--
isUnrefTypeVar :: Ident -> CheckState Bool
isUnrefTypeVar id
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     maybe True
		           (not . variableVisited)
		           (lookupSE (commonId id) senv)))

--
returnUnrefVars :: CheckState [Ident]
returnUnrefVars 
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     map (unqualify . fst)
		         (filter (not . variableVisited . snd) 
			         (toLevelListSE senv))))

--
beginScope :: CheckState ()
beginScope = CheckState (\msgs senv
			 -> (msgs,
			     beginScopeSE senv,
			     ()))

--
endScope :: CheckState ()
endScope = CheckState (\msgs senv
		       -> (msgs,
			   endScopeSE senv,
			   ()))


-- Adds the content of a value environment to the scope environment
addImports :: ValueEnv -> CheckState ()
addImports tyEnv = foldM' insertQualId (map fst (allImports tyEnv))

--
foldM' :: (a -> CheckState ()) -> [a] -> CheckState ()
foldM' f xs = foldM (\_ x -> f x) () xs

--
when' :: (CheckState Bool) -> CheckState () -> CheckState ()
when' mcond action = mcond >>= (\cond -> when cond action)

--
unless' :: (CheckState Bool) -> CheckState () -> CheckState ()
unless' mcond action = mcond >>= (\cond -> unless cond action)

--
dropUnless' :: (a -> CheckState Bool) -> [a] -> CheckState [a]
dropUnless' mpred [] = return []
dropUnless' mpred (x:xs)
   = do p <- mpred x
	if p then return (x:xs) else dropUnless' mpred xs

--
partition' :: (a -> CheckState Bool) -> [a] -> CheckState ([a],[a])
partition' mpred xs = part mpred [] [] xs
 where
 part mpred ts fs [] = return (reverse ts, reverse fs)
 part mpred ts fs (x:xs)
   = do p <- mpred x
	if p then part mpred (x:ts) fs xs
	     else part mpred ts (x:fs) xs

--
all' :: (a -> CheckState Bool) -> [a] -> CheckState Bool
all' mpred [] = return True
all' mpred (x:xs)
   = do p <- mpred x
	if p then all' mpred xs else return False


-- Runs a 'CheckState' action and returns the list of messages
run ::  CheckState a -> [Message CompMessageType]
run (CheckState f)
   = case (f [] newSE) of
       (m,_,_) -> reverse m


-------------------------------------------------------------------------------

-- Message kinds for compiler messages
data CompMessageType = Warning Position 
		     | Error Position 
		       deriving Eq


-- An instance of Show for converting the messages kinds to reasonable 
-- strings
instance Show CompMessageType where
 show (Warning pos) = "Warning: " ++ show pos ++ ": "
 show (Error pos)   = "ERROR: " ++ show pos ++ ": "


-- The following function generates several warning strings

unrefTypeVar :: Ident -> String
unrefTypeVar id = "unreferenced type variable \"" ++ show id ++ "\""

unrefVar :: Ident -> String
unrefVar id = "unreferenced variable \"" ++ show id ++ "\""

shadowingVar :: Ident -> String
shadowingVar id = "shadowing symbol \"" ++ show id ++ "\""

idleCaseAlts :: String
idleCaseAlts = "idle case alternative(s)"

overlappingCaseAlt :: String
overlappingCaseAlt = "redundant overlapping case alternative"

-------------------------------------------------------------------------------

--
isAnnonId :: Ident -> Bool
isAnnonId id = (name id) == "_"



-- Since type identifiers and normal identifiers (e.g. functions, variables
-- or constructors) don't share the same namespace, it is necessary
-- to distinguish them in the scope environment of the check state.
-- For this reason type identifiers are annotated with 1 and normal
-- identifiers are annotated with 0.
--
commonId :: Ident -> QualIdent
commonId id = qualify (unRenameIdent id)

--
typeId :: Ident -> QualIdent
typeId id = qualify (renameIdent id 1)


-- A safer version of 'tail'
tail_ :: [a] -> [a]
tail_ []     = []
tail_ (_:xs) = xs

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for representing a stack containing information from nested
-- scope levels
data ScopeEnv a b = ScopeEnv Int (Env a (b,Int)) [Env a (b,Int)]
		    deriving Show


--
newSE :: Ord a => ScopeEnv a b
newSE = ScopeEnv 0 emptyEnv []


-- Inserts a value under a key into the environment of the current level
insertSE :: Ord a => a -> b -> ScopeEnv a b -> ScopeEnv a b
insertSE key val env = modify insertLev env
 where
 insertLev lev local = bindEnv key (val,lev) local


-- Updates the value of an existing key in the environment of the current level
updateSE :: Ord a => a -> b -> ScopeEnv a b -> ScopeEnv a b
updateSE key val env = modify updateLev env
 where
 updateLev lev local = maybe local 
		             (\ (_,lev') ->  bindEnv key (val,lev') local)
			     (lookupEnv key local)

--
modifySE :: Ord a => (b -> b) -> a -> ScopeEnv a b -> ScopeEnv a b
modifySE fun key env = modify modifyLev env
 where
 modifyLev lev local 
    = maybe local
            (\ (val',lev') -> bindEnv key (fun val', lev') local)
	    (lookupEnv key local)


--
lookupSE :: Ord a => a -> ScopeEnv a b -> Maybe b
lookupSE key env = select lookupLev env
 where
 lookupLev lev local = maybe Nothing (Just . fst) (lookupEnv key local)


--
sureLookupSE :: Ord a => a -> b -> ScopeEnv a b -> b
sureLookupSE key alt env = maybe alt id (lookupSE key env)


--
levelSE :: Ord a => a -> ScopeEnv a b -> Int
levelSE key env = select levelLev env
 where
 levelLev lev local = maybe (-1) snd (lookupEnv key local)


--
existsSE :: Ord a => a -> ScopeEnv a b -> Bool
existsSE key env = select existsLev env
 where
 existsLev lev local = maybe False (const True) (lookupEnv key local)


-- Pushes the current scope onto the top of the stack and increments the
-- level counter
beginScopeSE :: Ord a => ScopeEnv a b -> ScopeEnv a b
beginScopeSE (ScopeEnv lev top [])
   = ScopeEnv (lev + 1) top [top]
beginScopeSE (ScopeEnv lev top (local:locals))
   = ScopeEnv (lev + 1) top (local:local:locals)


-- Pops the current scope from the top of the stack, updates the subjacent
-- scope (i.e. maintains the values from the poped scope for all keys in
-- the subjacent scope) and decrements the level counter.
endScopeSE :: Ord a => ScopeEnv a b -> ScopeEnv a b
endScopeSE (ScopeEnv _ top [])
   = ScopeEnv 0 top []
endScopeSE (ScopeEnv lev top (local:[]))
   = ScopeEnv 0 (foldr (update local) top (envToList top)) []
endScopeSE (ScopeEnv lev top (local:local':locals))
   = ScopeEnv (lev - 1) 
              top 
	      ((foldr (update local) local' (envToList local')):locals)


-- Returns the current scope as a list
toListSE :: Ord a => ScopeEnv a b -> [(a,b)]
toListSE env = select toListLev env
 where
 toListLev lev local = map (\ (key,(val,_)) -> (key,val)) (envToList local)

-- Returns all (key,value) pairs of the current scope which has been inserted
-- in the current level
toLevelListSE :: Ord a => ScopeEnv a b -> [(a,b)]
toLevelListSE env = select toLevelListLev env
 where
 toLevelListLev lev local
    = map (\ (key,(val,_)) -> (key,val))
          (filter (\ (_,(_,lev')) -> lev' == lev) (envToList local))


--
currentLevelSE :: Ord a => ScopeEnv a b -> Int
currentLevelSE env = select const env


-------------------------------------------------------------------------------

--
modify :: (Int -> Env a (b,Int) -> Env a (b,Int)) -> ScopeEnv a b 
          -> ScopeEnv a b
modify f (ScopeEnv _ top []) 
   = ScopeEnv 0 (f 0 top) []
modify f (ScopeEnv lev top (local:locals))
   = ScopeEnv lev top ((f lev local):locals)

--
select :: (Int -> Env a (b,Int) -> c) -> ScopeEnv a b -> c
select f (ScopeEnv _ top [])        = f 0 top
select f (ScopeEnv lev _ (local:_)) = f lev local

--
update :: Ord a => Env a (b,Int) -> (a,(b,Int)) ->  Env a (b,Int) 
          -> Env a (b,Int)
update local (key,(_,lev)) local'
   = maybe local' 
           (\ (val',lev') 
	    -> if lev == lev' then bindEnv key (val',lev) local' 
                              else local')
	   (lookupEnv key local)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------