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
import Message
import Env
import Monad


-------------------------------------------------------------------------------

warnCheck :: Module -> [Message CompMessageType]
warnCheck (Module mid _ decls)
   = run (checkDecls mid decls)

-- Die Importdecls getrennt betrachten.

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- The following functions check a curry program (in 'CurrySyntax' 
-- representation) for unreferenced and shadowing variables

checkDecls :: ModuleIdent -> [Decl] -> CheckState ()
checkDecls  mid decls
   = do foldM' insertDecl decls
	foldM' (checkDecl mid) decls

--
checkDecl :: ModuleIdent -> Decl -> CheckState ()
checkDecl mid (DataDecl pos ident params cdecls)
   = do visitTypeId ident
	beginScope
	foldM' insertTypeId params
	foldM' (checkConstrDecl mid) cdecls
	params' <- filterM isUnrefTypeId params
	when (not (null params')) 
	     (foldM' (genWarning pos) (map unrefTypeVar params'))
	endScope
checkDecl mid (TypeDecl pos ident params texpr)
   = do visitTypeId ident
	beginScope
	foldM' insertTypeId params
	checkTypeExpr mid pos texpr
	params' <- filterM isUnrefTypeId params
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
   = do idents' <- filterM isShadowingId idents
	when (not (null idents'))
	     (foldM' (genWarning pos) (map shadowingVar idents'))
	foldM' insertId idents
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
checktypeExpr mid pos (TupleType texprs)
   = foldM' (checkTypeExpr mid pos) texprs
checktypeExpr mid pos (ListType texpr)
   = checkTypeExpr mid pos texpr
checktypeExpr mid pos (ArrowType texpr1 texpr2)
   = do checkTypeExpr mid pos texpr1
	checkTypeExpr mid pos texpr2

--
checkEquation :: ModuleIdent -> Equation -> CheckState ()
checkEquation mid (Equation pos lhs rhs)
   = do checkLhs mid pos lhs
	checkRhs mid rhs
	idents' <- returnUnrefIds
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
   = when' (isShadowingId ident) (genWarning pos (shadowingVar ident))
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
   = do when' (isShadowingId ident) (genWarning pos (shadowingVar ident))
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
   = do --foldM' (checkStatement mid pos) stmts -- weil wegen sequentiell (TODO)
	checkExpression mid pos expr
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
 --checkExpression mid pos (Lambda cterms expr)
 --   = return () -- TO BE DONE
 --checkExpression mid pos (Let decls expr)
 --   = return () -- TO BE DONE
 --checkExpression mid pos (Do stmts expr)
 --   = return () -- TO BE DONE
checkExpression mid pos (IfThenElse expr1 expr2 expr3)
   = foldM' (checkExpression mid pos) [expr1, expr2, expr3]
 --checkExpression mid pos (Case expr alts)
 --   = return () -- TO BE DONE
checkExpression _ _ _ = return ()


-------------------------------------------------------------------------------
-- The following actions updates the current state by adding identifiers
-- occuring in declaration left hand sides

--
insertDecl :: Decl -> CheckState ()
insertDecl (DataDecl _ ident _ cdecls)
   = do insertTypeId ident
	foldM' insertConstrDecl cdecls
insertDecl (TypeDecl _ ident _ _)
   = insertTypeId ident
insertDecl (FunctionDecl _ ident _)
   = insertId ident
insertDecl (ExternalDecl _ _ _ ident _)
   = insertId ident
insertDecl (FlatExternalDecl _ idents)
   = foldM' insertId idents
 --insertDecl (PatternDecl _ cterm _)
 --   = insertConstrTerm cterm
 --insertDecl (ExtraVariables _ idents)
 --   = foldM' insertId idents
insertDecl _ = return ()

--
insertConstrDecl :: ConstrDecl -> CheckState ()
insertConstrDecl (ConstrDecl _ _ ident _)
   = insertId ident
insertConstrDecl (ConOpDecl _ _ _ ident _)
   = insertId ident

--
insertConstrTerm :: ConstrTerm -> CheckState ()
insertConstrTerm (VariablePattern ident)
   = insertId ident
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
   = do insertId ident
	insertConstrTerm cterm
insertConstrTerm (LazyPattern cterm)
   = insertConstrTerm cterm
insertConstrTerm _ = return ()


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for representing the current state of checking for warnings.
-- The monadic representation makes it easier and safer to deal with the list
-- of warning and the scope environment.
data CheckState a 
   = CheckState ([Message CompMessageType] -> ScopeEnv Ident Bool
		 -> ([Message CompMessageType], ScopeEnv Ident Bool, a))


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
insertId :: Ident -> CheckState ()
insertId id 
   | isAnnonId id = return ()
   | otherwise = CheckState (\msgs senv
			     -> (msgs,
				 insertSE (unRenameIdent id) False senv,
				 ()))

-- Since type identifiers and normal identifiers (e.g. functions, variables
-- or constructors) don't share the same namespace, it is necessary
-- to distinguish them in the scope environment of the check state.
-- For this reason the unique name of type identifiers is annotated with 1
-- whereas normal identifiers are annotated with 0.
insertTypeId :: Ident -> CheckState ()
insertTypeId id
   | isAnnonId id = return ()
   | otherwise    = CheckState (\msgs senv
				-> (msgs,
				    insertSE (renameIdent id 1) False senv,
				    ()))

-- Sinnvoller waere hier eine Funktion, die nicht nur auf Existenz prueft,
-- sondern gleichzeiting auch noch die Level vergleicht.
--existsId :: Ident -> CheckState Bool
--existsId id = CheckState (\msgs senv
--			  -> (msgs,
--			      senv,
--			      existsSE (unRenameIdent id) senv))

--
isShadowingId :: Ident -> CheckState Bool
isShadowingId id 
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     (existsSE id' senv
		      && levelSE id' senv < currentLevelSE senv)))
 where id' = unRenameIdent id

--
isShadowingTypeId :: Ident -> CheckState Bool
isShadowingTypeId id
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     (existsSE id' senv
		      && levelSE id' senv < currentLevelSE senv)))
 where id' = renameIdent id 1

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
			     updateSE (unRenameIdent id) True senv,
			     ()))

--
visitTypeId :: Ident -> CheckState ()
visitTypeId id = CheckState (\msgs senv
			     -> (msgs,
				 updateSE (renameIdent id 1) True senv,
				 ()))

--
isUnrefId :: Ident -> CheckState Bool
isUnrefId id 
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     maybe True not (lookupSE (unRenameIdent id) senv)))


--
isUnrefTypeId :: Ident -> CheckState Bool
isUnrefTypeId id
   = CheckState (\msgs senv
		 -> (msgs,
		     senv,
		     maybe True not (lookupSE (renameIdent id 1) senv)))

--
returnUnrefIds :: CheckState [Ident]
returnUnrefIds = CheckState (\msgs senv
			     -> (msgs,
				 senv,
				 map fst (filter (not . snd) (toListSE senv))))

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

--
foldM' :: (a -> CheckState ()) -> [a] -> CheckState ()
foldM' f xs = foldM (\_ x -> f x) () xs

--
when' :: (CheckState Bool) -> CheckState () -> CheckState ()
when' mcond action = mcond >>= (\cond -> when cond action)


-- Runs a 'CheckState' action and returns the list of messages
run :: CheckState a -> [Message CompMessageType]
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
shadowingVar id = "shadowing variable \"" ++ show id ++ "\""


-------------------------------------------------------------------------------

--
isAnnonId :: Ident -> Bool
isAnnonId id = (name id) == "_"

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


--
beginScopeSE :: Ord a => ScopeEnv a b -> ScopeEnv a b
beginScopeSE (ScopeEnv lev top [])
   = ScopeEnv (lev + 1) top [top]
beginScopeSE (ScopeEnv lev top (local:locals))
   = ScopeEnv (lev + 1) top (local:local:locals)


--
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