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
import Base (ValueEnv, ValueInfo(..), qualLookupValue, lookupValue)
import TopEnv
import qualified ScopeEnv
import ScopeEnv (ScopeEnv)
import Message
import Env
import Monad
import List


-------------------------------------------------------------------------------

-- Find potentially incorrect code in a Curry program and generate
-- the following warnings for:
--    - unreferenced variables
--    - shadowing variables
--    - idle case alternatives
--    - overlapping case alternatives
--    - function rules which are not together
warnCheck :: ModuleIdent -> ValueEnv -> [Decl] -> [Decl] -> [Message]
warnCheck mid vals imports decls
   = run (do addImportedValues vals
	     addModuleId mid
	     checkImports imports
	     foldM' insertDecl decls
	     foldM' (checkDecl mid) decls
             checkDeclOccurances decls
	 )


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
checkDecl :: ModuleIdent -> Decl -> CheckState ()
checkDecl mid (DataDecl pos ident params cdecls)
   = do beginScope
	foldM' insertTypeVar params
	foldM' (checkConstrDecl mid) cdecls
	params' <- filterM isUnrefTypeVar params
	when (not (null params')) 
	     (foldM' (genWarning pos) (map unrefTypeVar params'))
	endScope
checkDecl mid (TypeDecl pos ident params texpr)
   = do beginScope
	foldM' insertTypeVar params
	checkTypeExpr mid pos texpr
	params' <- filterM isUnrefTypeVar params
	when (not (null params'))
	     (foldM' (genWarning pos) (map unrefTypeVar params'))
	endScope
checkDecl mid (FunctionDecl pos ident equs)
   = do beginScope
	foldM' (checkEquation mid) equs
	c <- isConsId ident
	idents' <- returnUnrefVars
	when (not (c || null idents')) 
             (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkDecl mid (PatternDecl pos cterm rhs)
   = do checkConstrTerm mid pos cterm
	checkRhs mid pos rhs
checkDecl _ _ = return ()

-- Checks locally declared identifiers (i.e. functions and logic variables)
-- for shadowing
checkLocalDecl :: Decl -> CheckState ()
checkLocalDecl (FunctionDecl pos ident _)
   = do s <- isShadowingVar ident
	when s (genWarning pos (shadowingVar ident))
checkLocalDecl (ExtraVariables pos idents)
   = do idents' <- filterM isShadowingVar idents
	when (not (null idents'))
	     (foldM' (genWarning pos) (map shadowingVar idents'))
checkLocalDecl _ = return ()

--
checkConstrDecl :: ModuleIdent -> ConstrDecl -> CheckState ()
checkConstrDecl mid (ConstrDecl pos _ ident texprs)
   = do visitId ident
	foldM' (checkTypeExpr mid pos) texprs
checkConstrDecl mid (ConOpDecl pos _ texpr1 ident texpr2)
   = do visitId ident
	checkTypeExpr mid pos texpr1
	checkTypeExpr mid pos texpr2


checkTypeExpr :: ModuleIdent -> Position -> TypeExpr -> CheckState ()
checkTypeExpr mid pos (ConstructorType qid texprs)
   = do maybe (return ()) visitTypeId (localIdent mid qid)
	foldM' (checkTypeExpr mid pos) texprs
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
	checkRhs mid pos rhs

--
checkLhs :: ModuleIdent -> Position -> Lhs -> CheckState ()
checkLhs mid pos (FunLhs ident cterms)
   = do visitId ident
	foldM' (checkConstrTerm mid pos) cterms
	foldM' (insertConstrTerm False) cterms
checkLhs mid pos (OpLhs cterm1 ident cterm2)
   = checkLhs mid pos (FunLhs ident [cterm1, cterm2])
checkLhs mid pos (ApLhs lhs cterms)
   = do checkLhs mid pos lhs
	foldM' (checkConstrTerm mid pos) cterms
	foldM' (insertConstrTerm False) cterms

--
checkRhs :: ModuleIdent -> Position -> Rhs -> CheckState ()
checkRhs mid _ (SimpleRhs pos expr decls)
   = do beginScope  -- function arguments can be overwritten by local decls
	foldM' checkLocalDecl decls
	foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	checkDeclOccurances decls
	checkExpression mid pos expr
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkRhs mid pos (GuardedRhs cexprs decls)
   = do beginScope
	foldM' checkLocalDecl decls
	foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	checkDeclOccurances decls
	foldM' (checkCondExpr mid) cexprs
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope

--
checkCondExpr :: ModuleIdent -> CondExpr -> CheckState ()
checkCondExpr mid (CondExpr pos cond expr)
   = do checkExpression mid pos cond
	checkExpression mid pos expr

-- 
checkConstrTerm :: ModuleIdent -> Position -> ConstrTerm -> CheckState ()
checkConstrTerm mid pos (VariablePattern ident)
   = do s <- isShadowingVar ident
	when s (genWarning pos (shadowingVar ident))
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
   = do s <- isShadowingVar ident
	when s (genWarning pos (shadowingVar ident))
	checkConstrTerm mid pos cterm
checkConstrTerm mid pos (LazyPattern cterm)
   = checkConstrTerm mid pos cterm
checkConstrTerm mid pos (FunctionPattern _ cterms)
   = foldM' (checkConstrTerm mid pos) cterms
checkConstrTerm mid pos (InfixFuncPattern cterm1 qident cterm2)
   = checkConstrTerm mid pos (FunctionPattern qident [cterm1, cterm2])
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
checkExpression mid pos (InfixApply expr1 op expr2)
   = do maybe (return ()) (visitId) (localIdent mid (opName op))
	foldM' (checkExpression mid pos) [expr1, expr2]
checkExpression mid pos (LeftSection expr _)
   = checkExpression mid pos expr
checkExpression mid pos (RightSection _ expr)
   = checkExpression mid pos expr
checkExpression mid pos (Lambda cterms expr)
   = do beginScope
	foldM' (checkConstrTerm mid pos) cterms
	foldM' (insertConstrTerm False) cterms
	checkExpression mid pos expr
	idents' <- returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope
checkExpression mid pos (Let decls expr)
   = do beginScope
	foldM' checkLocalDecl decls
	foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	checkDeclOccurances decls
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
	foldM' (checkAlt mid) alts
	checkCaseAlternatives mid alts
checkExpression _ _ _ = return ()

--
checkStatement :: ModuleIdent -> Position -> Statement -> CheckState ()
checkStatement mid pos (StmtExpr expr)
   = checkExpression mid pos expr
checkStatement mid pos (StmtDecl decls)
   = do foldM' checkLocalDecl decls
	foldM' insertDecl decls
	foldM' (checkDecl mid) decls
	checkDeclOccurances decls
checkStatement mid pos (StmtBind cterm expr)
   = do checkConstrTerm mid pos cterm
	insertConstrTerm False cterm
	checkExpression mid pos expr

--
checkAlt :: ModuleIdent -> Alt -> CheckState ()
checkAlt mid (Alt pos cterm rhs)
   = do beginScope 
	checkConstrTerm mid pos cterm
	insertConstrTerm False cterm
	checkRhs mid pos rhs
	idents' <-  returnUnrefVars
	when (not (null idents'))
	     (foldM' (genWarning pos) (map unrefVar idents'))
	endScope

-- Check for idle and overlapping case alternatives
checkCaseAlternatives :: ModuleIdent -> [Alt] -> CheckState ()
checkCaseAlternatives mid alts
   = do checkIdleAlts mid alts
	checkOverlappingAlts mid alts

--
checkIdleAlts :: ModuleIdent -> [Alt] -> CheckState ()
checkIdleAlts mid alts
   = do alts' <- dropUnless' isVarAlt alts
	let idles = tail_ [] alts'
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
    = do p <- isConsId id1 
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
    = cmpListM equalConstrTerms cs1 cs2
 equalConstrTerms (AsPattern id1 cterm1) (AsPattern id2 cterm2)
    = equalConstrTerms cterm1 cterm2
 equalConstrTerms (LazyPattern cterm1) (LazyPattern cterm2)
    = equalConstrTerms cterm1 cterm2
 equalConstrTerms _ _ = return False


-- Find function rules which are not together
checkDeclOccurances :: [Decl] -> CheckState ()
checkDeclOccurances decls = checkDO (mkIdent "") emptyEnv decls
 where
 checkDO prevId env [] = return ()
 checkDO prevId env ((FunctionDecl pos ident _):decls)
    = do c <- isConsId ident
	 if not (c || prevId == ident)
          then (maybe (checkDO ident (bindEnv ident pos env) decls)
	              (\pos' -> genWarning pos (rulesNotTogether ident pos')
		                >> checkDO ident env decls)
	              (lookupEnv ident env))
	  else checkDO ident env decls
 checkDO _ env (_:decls) 
    = checkDO (mkIdent "") env decls


-- check import declarations for multiply imported modules
checkImports :: [Decl] -> CheckState ()
checkImports imps = checkImps emptyEnv imps
 where
 checkImps env [] = return ()
 checkImps env ((ImportDecl pos mid _ _ spec):imps)
    | mid /= preludeMIdent
      = maybe (checkImps (bindEnv mid (fromImpSpec spec) env) imps)
              (\ishs -> checkImpSpec env pos mid ishs spec
	                >>= (\env' -> checkImps env' imps))
	      (lookupEnv mid env)
    | otherwise
      = checkImps env imps
 checkImps env (_:imps) = checkImps env imps

 checkImpSpec env pos mid (is,hs) Nothing
    = genWarning pos (multiplyImportedModule mid) >> return env
 checkImpSpec env pos mid (is,hs) (Just (Importing pos' is'))
    | null is && any (\i' -> notElem i' hs) is'
      = do genWarning pos (multiplyImportedModule mid)
	   return (bindEnv mid (is',hs) env)
    | null iis
      = return (bindEnv mid (is' ++ is,hs) env)
    | otherwise
      = do foldM' (genWarning pos')
		  (map ((multiplyImportedSymbol mid) . impName) iis)
	   return (bindEnv mid (unionBy cmpImport is' is,hs) env)
  where iis = intersectBy cmpImport is' is
 checkImpSpec env pos mid (is,hs) (Just (Hiding pos' hs'))
    | null ihs
      = return (bindEnv mid (is,hs' ++ hs) env)
    | otherwise
      = do foldM' (genWarning pos)
		  (map ((multiplyHiddenSymbol mid) . impName) ihs)
	   return (bindEnv mid (is,unionBy cmpImport hs' hs) env)
  where ihs = intersectBy cmpImport hs' hs

 cmpImport (ImportTypeWith id1 cs1) (ImportTypeWith id2 cs2)
    = id1 == id2 && null (intersect cs1 cs2)
 cmpImport i1 i2 = (impName i1) == (impName i2)

 impName (Import id)           = id
 impName (ImportTypeAll id)    = id
 impName (ImportTypeWith id _) = id

 fromImpSpec Nothing                 = ([],[])
 fromImpSpec (Just (Importing _ is)) = (is,[])
 fromImpSpec (Just (Hiding _ hs))    = ([],hs)


-------------------------------------------------------------------------------
-- For detecting unreferenced variables, the following functions updates the 
-- current check state by adding identifiers occuring in declaration left hand 
-- sides.

--
insertDecl :: Decl -> CheckState ()
insertDecl (DataDecl _ ident _ cdecls)
   = do insertTypeConsId ident
	foldM' insertConstrDecl cdecls
insertDecl (TypeDecl _ ident _ _)
   = insertTypeConsId ident
insertDecl (FunctionDecl _ ident _)
   = do c <- isConsId ident
	unless c (insertVar ident)
insertDecl (ExternalDecl _ _ _ ident _)
   = insertVar ident
insertDecl (FlatExternalDecl _ idents)
   = foldM' insertVar idents
insertDecl (PatternDecl _ cterm _)
   = insertConstrTerm False cterm
insertDecl (ExtraVariables _ idents)
   = foldM' insertVar idents
insertDecl _ = return ()

--
insertConstrDecl :: ConstrDecl -> CheckState ()
insertConstrDecl (ConstrDecl _ _ ident _)
   = insertConsId ident
insertConstrDecl (ConOpDecl _ _ _ ident _)
   = insertConsId ident

-- Notes: 
--    - 'fp' indicates whether 'checkConstrTerm' deals with the arguments
--      of a function pattern or not.
--    - Since function patterns are not recognized before syntax check, it is
--      necessary to determine, whether a constructor pattern represents a
--      constructor or a function. 
insertConstrTerm :: Bool -> ConstrTerm -> CheckState ()
insertConstrTerm fp (VariablePattern ident)
   = do c <- isConsId ident
	unless (fp || c) (insertVar ident)
insertConstrTerm fp (ConstructorPattern qident cterms)
   = do c <- isQualConsId qident
	if c then foldM' (insertConstrTerm fp) cterms
	     else foldM' (insertConstrTerm True) cterms
insertConstrTerm fp (InfixPattern cterm1 qident cterm2)
   = insertConstrTerm fp (ConstructorPattern qident [cterm1, cterm2])
insertConstrTerm fp (ParenPattern cterm)
   = insertConstrTerm fp cterm
insertConstrTerm fp (TuplePattern cterms)
   = foldM' (insertConstrTerm fp) cterms
insertConstrTerm fp (ListPattern cterms)
   = foldM' (insertConstrTerm fp) cterms
insertConstrTerm fp (AsPattern ident cterm)
   = do insertVar ident
	insertConstrTerm fp cterm
insertConstrTerm fp (LazyPattern cterm)
   = insertConstrTerm fp cterm
insertConstrTerm _ (FunctionPattern _ cterms)
   = foldM' (insertConstrTerm True) cterms
insertConstrTerm _ (InfixFuncPattern cterm1 qident cterm2)
   = insertConstrTerm True (FunctionPattern qident [cterm1, cterm2])
insertConstrTerm _ _ = return ()


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for distinguishing identifiers as either (type) constructors or
-- (type) variables (including functions).
-- The Boolean flag in 'VarInfo' is used to mark variables when they are used 
-- within expressions.
data IdInfo = ConsInfo | VarInfo Bool deriving Show

--
isVariable :: IdInfo -> Bool
isVariable (VarInfo _) = True
isVariable _           = False

--
isConstructor :: IdInfo -> Bool
isConstructor ConsInfo = True
isConstructor _        = False

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
-- The monadic representation of the state allows the usage of monadic 
-- syntax (do expression) for dealing easier and safer with its
-- contents.
data CheckState a = CheckState (CState () -> CState a)

data CState a = CState {messages  :: [Message],
			scope     :: ScopeEnv QualIdent IdInfo,
			values    :: ValueEnv,
			moduleId  :: ModuleIdent,
			result    :: a
		       }

--
emptyState :: CState ()
emptyState = CState {messages  = [],
		     scope     = ScopeEnv.new,
		     values    = emptyTopEnv,
		     moduleId  = mkMIdent [],
		     result    = ()
		    }

--
modifyScope :: (ScopeEnv QualIdent IdInfo -> ScopeEnv QualIdent IdInfo)
	       -> CState a -> CState a
modifyScope f state = state{ scope = f (scope state) }


-- 'CheckState' is declared as an instance of 'Monad' to use its actions
-- in 'do' expressions
instance Monad CheckState where

 -- (>>=) :: CheckState a -> (a -> CheckState b) -> CheckState b
 (CheckState f) >>= g 
    = CheckState (\state -> let state'       = f state
		                CheckState h = g (result state')
		            in  h (state'{ result = () }))

 -- (>>) :: CheckState a -> CheckState b -> CheckState b
 a >> b = a >>= (\_ -> b)

 -- return :: a -> CheckState a
 return val = CheckState (\state -> state{ result = val })


--
genWarning :: Position -> String -> CheckState ()
genWarning pos msg
   = CheckState (\state -> state{ messages = warnMsg:(messages state) })
 where warnMsg = message Warning pos msg

--
insertVar :: Ident -> CheckState ()
insertVar id 
   | isAnnonId id = return ()
   | otherwise
     = CheckState 
         (\state -> modifyScope 
	              (ScopeEnv.insert (commonId id) (VarInfo False)) state)

--
insertTypeVar :: Ident -> CheckState ()
insertTypeVar id
   | isAnnonId id = return ()
   | otherwise    
     = CheckState 
         (\state -> modifyScope 
	              (ScopeEnv.insert (typeId id) (VarInfo False)) state)

--
insertConsId :: Ident -> CheckState ()
insertConsId id
   = CheckState 
       (\state -> modifyScope (ScopeEnv.insert (commonId id) ConsInfo) state)

--
insertTypeConsId :: Ident -> CheckState ()
insertTypeConsId id
   = CheckState 
       (\state -> modifyScope (ScopeEnv.insert (typeId id) ConsInfo) state)

--
isVarId :: Ident -> CheckState Bool
isVarId id
   = CheckState (\state -> state{ result = isVar state (commonId id) })

--
isConsId :: Ident -> CheckState Bool
isConsId id 
   = CheckState (\state -> state{ result = isCons state (qualify id) })

--
isQualConsId :: QualIdent -> CheckState Bool
isQualConsId qid
   = CheckState (\state -> state{ result = isCons state qid })

--
isShadowingVar :: Ident -> CheckState Bool
isShadowingVar id 
   = CheckState 
       (\state -> state{ result = isShadowing state (commonId id) })

--
isShadowingTypeVar :: Ident -> CheckState Bool
isShadowingTypeVar id
   = CheckState 
       (\state -> state{ result = isShadowing state (typeId id) })

--
visitId :: Ident -> CheckState ()
visitId id 
   = CheckState 
       (\state -> modifyScope 
	            (ScopeEnv.modify visitVariable (commonId id)) state)

--
visitTypeId :: Ident -> CheckState ()
visitTypeId id 
   = CheckState 
       (\state -> modifyScope 
	            (ScopeEnv.modify visitVariable (typeId id)) state)

--
isUnrefVar :: Ident -> CheckState Bool
isUnrefVar id 
   = CheckState (\state -> state{ result = isUnref state (commonId id) })

--
isUnrefTypeVar :: Ident -> CheckState Bool
isUnrefTypeVar id
   = CheckState (\state -> state{ result = isUnref state (typeId id) })

--
returnUnrefVars :: CheckState [Ident]
returnUnrefVars 
   = CheckState (\state -> 
	   	    let ids    = map fst (ScopeEnv.toLevelList (scope state))
                        unrefs = filter (isUnref state) ids
	            in  state{ result = map unqualify unrefs })

--
addModuleId :: ModuleIdent -> CheckState ()
addModuleId mid = CheckState (\state -> state{ moduleId = mid })

--
returnModuleId :: CheckState ModuleIdent
returnModuleId = CheckState (\state -> state{ result = moduleId state })

--
beginScope :: CheckState ()
beginScope = CheckState (\state -> modifyScope ScopeEnv.beginScope state)

--
endScope :: CheckState ()
endScope = CheckState (\state -> modifyScope ScopeEnv.endScopeUp state)


-- Adds the content of a value environment to the state
addImportedValues :: ValueEnv -> CheckState ()
addImportedValues vals = CheckState (\state -> state{ values = vals })

--
foldM' :: (a -> CheckState ()) -> [a] -> CheckState ()
foldM' f [] = return ()
foldM' f (x:xs) = f x >> foldM' f xs

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
run ::  CheckState a -> [Message]
run (CheckState f)
   = reverse (messages (f emptyState))


-------------------------------------------------------------------------------

--
isShadowing :: CState a -> QualIdent -> Bool
isShadowing state qid
   = let sc = scope state
     in  maybe False isVariable (ScopeEnv.lookup qid sc)
	 && ScopeEnv.level qid sc < ScopeEnv.currentLevel sc

--
isUnref :: CState a -> QualIdent -> Bool
isUnref state qid 
   = let sc = scope state
     in  maybe False (not . variableVisited) (ScopeEnv.lookup qid sc)
         && ScopeEnv.level qid sc == ScopeEnv.currentLevel sc

--
isVar :: CState a -> QualIdent -> Bool
isVar state qid = maybe (isAnnonId (unqualify qid)) 
	           isVariable 
		   (ScopeEnv.lookup qid (scope state))

--
isCons :: CState a -> QualIdent -> Bool
isCons state qid = maybe (isImportedCons state qid)
		         isConstructor
			 (ScopeEnv.lookup qid (scope state))
 where
 isImportedCons state qid
    = case (qualLookupValue qid (values state)) of
        (DataConstructor _ _):_    -> True
        (NewtypeConstructor _ _):_ -> True
        _                          -> False


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


-------------------------------------------------------------------------------
-- Warnings...

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

rulesNotTogether :: Ident -> Position -> String
rulesNotTogether id pos
   = "rules for function \"" ++ show id ++ "\" are not together "
     ++ "(first occurance at " 
     ++ show (line pos) ++ "." ++ show (column pos) ++ ")"

multiplyImportedModule :: ModuleIdent -> String
multiplyImportedModule mid 
   = "module \"" ++ show mid ++ "\" was imported more than once"

multiplyImportedSymbol :: ModuleIdent -> Ident -> String
multiplyImportedSymbol mid ident
   = "symbol \"" ++ show ident ++ "\" was imported from module \""
     ++ show mid ++ "\" more than once"

multiplyHiddenSymbol :: ModuleIdent -> Ident -> String
multiplyHiddenSymbol mid ident
   = "symbol \"" ++ show ident ++ "\" from module \"" ++ show mid
     ++ "\" was hidden more than once"


-------------------------------------------------------------------------------
-- Miscellaneous

-- safer versions of 'tail' and 'head'
tail_ :: [a] -> [a] -> [a]
tail_ alt []     = alt
tail_ _   (_:xs) = xs

head_ :: a -> [a] -> a
head_ alt []    = alt
head_ _   (x:_) = x

--
cmpListM :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m Bool
cmpListM cmpM []     []     = return True
cmpListM cmpM (x:xs) (y:ys) = do c <- cmpM x y
				 if c then cmpListM cmpM xs ys 
				      else return False
cmpListM cmpM _      _      = return False


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------