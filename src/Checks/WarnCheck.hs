{- |
    Module      :  $Header$
    Description :  Checks for irregular code
    Copyright   :  (c) 2006, Martin Engelke (men@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module searches for potentially irregular code and generates
    warning messages.
-}
module Checks.WarnCheck (warnCheck) where

import Control.Monad.State (State, execState, filterM, gets, modify, unless, when, foldM_)
import qualified Data.Map as Map (empty, insert, lookup)
import Data.List (intersect, intersectBy, unionBy)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.MessageMonad
import Curry.Syntax

import qualified Base.ScopeEnv as ScopeEnv

import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)


-- Current state of generating warnings
data CState = CState
  { messages  :: [Message]
  , scope     :: ScopeEnv.ScopeEnv QualIdent IdInfo
  , values    :: ValueEnv
  , moduleId  :: ModuleIdent
  }

-- The monadic representation of the state allows the usage of monadic
-- syntax (do expression) for dealing easier and safer with its
-- contents.
type CheckM = State CState

initCState :: ModuleIdent -> ValueEnv -> CState
initCState mid valueEnv = CState [] ScopeEnv.new valueEnv mid

checked :: CheckM ()
checked = return ()

-- |Run a 'CheckM' action and return the list of messages
runOn :: CState -> CheckM a -> [Message]
runOn s f = reverse $ messages $ execState f s

-- Find potentially incorrect code in a Curry program and generate
-- the following warnings for:
--    - unreferenced variables
--    - shadowing variables
--    - idle case alternatives
--    - overlapping case alternatives
--    - function rules which are not together
warnCheck :: ModuleIdent -> ValueEnv -> [ImportDecl] -> [Decl] -> [Message]
warnCheck mid vals imports decls = runOn (initCState mid vals) $ do
  checkForMultipleImports imports
  mapM_ insertDecl decls
  mapM_ (checkDecl mid) decls
  checkDeclOccurrences decls

-- ---------------------------------------------------------------------------
-- checkForMultipleImports
-- ---------------------------------------------------------------------------

-- check import declarations for multiply imported modules
--
-- The function uses a map of the already imported or hidden entities to
-- collect the entities throughout multiple import statements.
checkForMultipleImports :: [ImportDecl] -> CheckM ()
checkForMultipleImports imps = foldM_ checkImport Map.empty imps
  where
  checkImport env (ImportDecl pos mid _ _ spec) = case Map.lookup mid env of
    Nothing   -> setImportSpec env mid $ fromImpSpec spec
    Just ishs -> checkImportSpec env pos mid ishs spec

  checkImportSpec env _ mid (_, _) Nothing = do
    genWarning' $ multiplyImportedModule mid
    return env

  checkImportSpec env _ mid (is, hs) (Just (Importing _ is'))
    | null is && any (`notElem` hs) is' = do
        genWarning' $ multiplyImportedModule mid
        setImportSpec env mid (is', hs)
    | null iis  = setImportSpec env mid (is' ++ is, hs)
    | otherwise = do
        mapM_ (genWarning' . (multiplyImportedSymbol mid) . impName) iis
        setImportSpec env mid (unionBy cmpImport is' is, hs)
    where iis = intersectBy cmpImport is' is

  checkImportSpec env _ mid (is, hs) (Just (Hiding _ hs'))
    | null ihs  = setImportSpec env mid (is, hs' ++ hs)
    | otherwise = do
      mapM_ (genWarning' . (multiplyHiddenSymbol mid) . impName) ihs
      setImportSpec env mid (is, unionBy cmpImport hs' hs)
    where ihs = intersectBy cmpImport hs' hs

  fromImpSpec Nothing                 = ([], [])
  fromImpSpec (Just (Importing _ is)) = (is, [])
  fromImpSpec (Just (Hiding    _ hs)) = ([], hs)

  setImportSpec env mid ishs = return $ Map.insert mid ishs env

  cmpImport (ImportTypeWith id1 cs1) (ImportTypeWith id2 cs2)
    = id1 == id2 && null (intersect cs1 cs2)
  cmpImport i1 i2 = (impName i1) == (impName i2)

  impName (Import           ident) = ident
  impName (ImportTypeAll    ident) = ident
  impName (ImportTypeWith ident _) = ident

-- ---------------------------------------------------------------------------
-- checkDeclOccurrences
-- ---------------------------------------------------------------------------

-- Find function rules which are not together
checkDeclOccurrences :: [Decl] -> CheckM ()
checkDeclOccurrences decls = foldM_ checkDO (mkIdent "", Map.empty) decls
  where
  checkDO (prevId, env) (FunctionDecl pos ident _) = do
    c <- isConsId ident
    if c || prevId == ident
      then return (ident, env)
      else case Map.lookup ident env of
        Nothing   -> return (ident, Map.insert ident pos env)
        Just pos' -> do
          genWarning' $ rulesNotTogether ident pos'
          return (ident, env)
  checkDO (_, env) _ = return (mkIdent "", env)

-- ---------------------------------------------------------------------------
-- do something else
-- ---------------------------------------------------------------------------

--
checkDecl :: ModuleIdent -> Decl -> CheckM ()
checkDecl mid (DataDecl _ _ params cdecls) = withScope $ do
  mapM_ insertTypeVar params
  mapM_ (checkConstrDecl mid) cdecls
  params' <- filterM isUnrefTypeVar params
  when (not $ null params') $ mapM_ genWarning' $ map unrefTypeVar params'
checkDecl mid (TypeDecl _ _ params texpr) = withScope $ do
  mapM_ insertTypeVar params
  checkTypeExpr mid texpr
  params' <- filterM isUnrefTypeVar params
  when (not $ null params') $ mapM_ genWarning' $ map unrefTypeVar params'
checkDecl mid (FunctionDecl _ ident equs) = withScope $ do
  mapM_ (checkEquation mid) equs
  c <- isConsId ident
  idents' <- returnUnrefVars
  when (not $ c || null idents') $ mapM_ genWarning' $ map unrefVar idents'
checkDecl mid (PatternDecl _ cterm rhs) = do
  checkConstrTerm mid cterm
  checkRhs mid rhs
checkDecl _ _ = checked

-- Checks locally declared identifiers (i.e. functions and logic variables)
-- for shadowing
checkLocalDecl :: Decl -> CheckM ()
checkLocalDecl (FunctionDecl _ ident _) = do
  s <- isShadowingVar ident
  when s $ genWarning' $ shadowingVar ident
checkLocalDecl (ExtraVariables _ idents) = do
  idents' <- filterM isShadowingVar idents
  when (not $ null idents') $ mapM_ genWarning' $ map shadowingVar idents'
checkLocalDecl (PatternDecl _ constrTerm _)
  = checkConstrTerm (mkMIdent []) constrTerm
checkLocalDecl _ = checked

--
checkConstrDecl :: ModuleIdent -> ConstrDecl -> CheckM ()
checkConstrDecl mid (ConstrDecl _ _ ident texprs) = do
  visitId ident
  mapM_ (checkTypeExpr mid) texprs
checkConstrDecl mid (ConOpDecl _ _ texpr1 ident texpr2) = do
  visitId ident
  checkTypeExpr mid texpr1
  checkTypeExpr mid texpr2


checkTypeExpr :: ModuleIdent -> TypeExpr -> CheckM ()
checkTypeExpr mid (ConstructorType qid texprs) = do
  maybe checked visitTypeId (localIdent mid qid)
  mapM_ (checkTypeExpr mid) texprs
checkTypeExpr _   (VariableType ident)
  = visitTypeId ident
checkTypeExpr mid (TupleType texprs)
  = mapM_ (checkTypeExpr mid) texprs
checkTypeExpr mid (ListType texpr)
  = checkTypeExpr mid texpr
checkTypeExpr mid (ArrowType texpr1 texpr2) = do
  checkTypeExpr mid texpr1
  checkTypeExpr mid texpr2
checkTypeExpr mid (RecordType fields restr) = do
  mapM_ (checkTypeExpr mid ) (map snd fields)
  maybe checked (checkTypeExpr mid) restr

--
checkEquation :: ModuleIdent -> Equation -> CheckM ()
checkEquation mid (Equation _ lhs rhs) = do
  checkLhs mid lhs
  checkRhs mid rhs

--
checkLhs :: ModuleIdent -> Lhs -> CheckM ()
checkLhs mid (FunLhs ident cterms) = do
  visitId ident
  mapM_ (checkConstrTerm mid) cterms
  mapM_ (insertConstrTerm False) cterms
checkLhs mid (OpLhs cterm1 ident cterm2)
  = checkLhs mid (FunLhs ident [cterm1, cterm2])
checkLhs mid (ApLhs lhs cterms) = do
  checkLhs mid lhs
  mapM_ (checkConstrTerm mid ) cterms
  mapM_ (insertConstrTerm False) cterms

--
checkRhs :: ModuleIdent -> Rhs -> CheckM ()
checkRhs mid (SimpleRhs _ expr decls) = withScope $ do -- function arguments can be overwritten by local decls
  mapM_ checkLocalDecl decls
  mapM_ insertDecl decls
  mapM_ (checkDecl mid) decls
  checkDeclOccurrences decls
  checkExpression mid expr
  idents' <- returnUnrefVars
  when (not $ null idents') $ mapM_ genWarning' $ map unrefVar idents'
checkRhs mid (GuardedRhs cexprs decls) = withScope $ do
  mapM_ checkLocalDecl decls
  mapM_ insertDecl decls
  mapM_ (checkDecl mid) decls
  checkDeclOccurrences decls
  mapM_ (checkCondExpr mid) cexprs
  idents' <- returnUnrefVars
  when (not $ null idents') $  mapM_ genWarning' $ map unrefVar idents'

--
checkCondExpr :: ModuleIdent -> CondExpr -> CheckM ()
checkCondExpr mid (CondExpr _ cond expr) = do
  checkExpression mid cond
  checkExpression mid expr

--
checkConstrTerm :: ModuleIdent -> ConstrTerm -> CheckM ()
checkConstrTerm _ (VariablePattern ident) = do
  s <- isShadowingVar ident
  when s $ genWarning' $ shadowingVar ident
checkConstrTerm mid (ConstructorPattern _ cterms)
  = mapM_ (checkConstrTerm mid ) cterms
checkConstrTerm mid (InfixPattern cterm1 qident cterm2)
  = checkConstrTerm mid (ConstructorPattern qident [cterm1, cterm2])
checkConstrTerm mid (ParenPattern cterm)
  = checkConstrTerm mid cterm
checkConstrTerm mid (TuplePattern _ cterms)
  = mapM_ (checkConstrTerm mid ) cterms
checkConstrTerm mid (ListPattern _ cterms)
  = mapM_ (checkConstrTerm mid ) cterms
checkConstrTerm mid (AsPattern ident cterm) = do
  s <- isShadowingVar ident
  when s $ genWarning' $ shadowingVar ident
  checkConstrTerm mid cterm
checkConstrTerm mid (LazyPattern _ cterm)
  = checkConstrTerm mid cterm
checkConstrTerm mid (FunctionPattern _ cterms)
  = mapM_ (checkConstrTerm mid ) cterms
checkConstrTerm mid  (InfixFuncPattern cterm1 qident cterm2)
  = checkConstrTerm mid  (FunctionPattern qident [cterm1, cterm2])
checkConstrTerm mid  (RecordPattern fields restr) = do
  mapM_ (checkFieldPattern mid) fields
  maybe checked (checkConstrTerm mid) restr
checkConstrTerm _ _ = return ()

--
checkExpression :: ModuleIdent -> Expression -> CheckM ()
checkExpression mid (Variable qident)
  = maybe (return ()) visitId (localIdent mid qident)
checkExpression mid (Paren expr)
  = checkExpression mid expr
checkExpression mid (Typed expr _)
  = checkExpression mid expr
checkExpression mid (Tuple _ exprs)
  = mapM_ (checkExpression mid ) exprs
checkExpression mid (List _ exprs)
  = mapM_ (checkExpression mid ) exprs
checkExpression mid (ListCompr _ expr stmts) = withScope $ do
  mapM_ (checkStatement mid) stmts
  checkExpression mid expr
  idents' <- returnUnrefVars
  when (not $ null idents') $ mapM_ genWarning' $ map unrefVar idents'
checkExpression mid  (EnumFrom expr)
  = checkExpression mid  expr
checkExpression mid  (EnumFromThen expr1 expr2)
  = mapM_ (checkExpression mid ) [expr1, expr2]
checkExpression mid  (EnumFromTo expr1 expr2)
  = mapM_ (checkExpression mid ) [expr1, expr2]
checkExpression mid  (EnumFromThenTo expr1 expr2 expr3)
  = mapM_ (checkExpression mid ) [expr1, expr2, expr3]
checkExpression mid  (UnaryMinus _ expr)
  = checkExpression mid  expr
checkExpression mid  (Apply expr1 expr2)
  = mapM_ (checkExpression mid ) [expr1, expr2]
checkExpression mid  (InfixApply expr1 op expr2) = do
  maybe checked (visitId) (localIdent mid (opName op))
  mapM_ (checkExpression mid ) [expr1, expr2]
checkExpression mid  (LeftSection expr _)
  = checkExpression mid  expr
checkExpression mid  (RightSection _ expr)
  = checkExpression mid  expr
checkExpression mid  (Lambda _ cterms expr) = withScope $ do
  mapM_ (checkConstrTerm mid ) cterms
  mapM_ (insertConstrTerm False) cterms
  checkExpression mid expr
  idents' <- returnUnrefVars
  when (not $ null idents') $ mapM_ genWarning' $ map unrefVar idents'
checkExpression mid  (Let decls expr) = withScope $ do
  mapM_ checkLocalDecl decls
  mapM_ insertDecl decls
  mapM_ (checkDecl mid) decls
  checkDeclOccurrences decls
  checkExpression mid  expr
  idents' <- returnUnrefVars
  when (not $ null idents') $ mapM_ genWarning' $ map unrefVar idents'
checkExpression mid  (Do stmts expr) = withScope $ do
  mapM_ (checkStatement mid ) stmts
  checkExpression mid  expr
  idents' <- returnUnrefVars
  when (not $ null idents') $ mapM_ genWarning' $ map unrefVar idents'
checkExpression mid  (IfThenElse _ expr1 expr2 expr3)
  = mapM_ (checkExpression mid ) [expr1, expr2, expr3]
checkExpression mid  (Case _ expr alts) = do
  checkExpression mid  expr
  mapM_ (checkAlt mid) alts
  checkCaseAlternatives mid alts
checkExpression mid (RecordConstr fields)
  = mapM_ (checkFieldExpression mid) fields
checkExpression mid (RecordSelection expr _)
  = checkExpression mid expr -- Hier auch "visitId ident" ?
checkExpression mid (RecordUpdate fields expr) = do
  mapM_ (checkFieldExpression mid) fields
  checkExpression mid expr
checkExpression _ _  = checked

--
checkStatement :: ModuleIdent -> Statement -> CheckM ()
checkStatement mid (StmtExpr _ expr)
   = checkExpression mid expr
checkStatement mid (StmtDecl decls) = do
  mapM_ checkLocalDecl decls
  mapM_ insertDecl decls
  mapM_ (checkDecl mid) decls
  checkDeclOccurrences decls
checkStatement mid (StmtBind _ cterm expr) = do
  checkConstrTerm mid cterm
  insertConstrTerm False cterm
  checkExpression mid expr

--
checkAlt :: ModuleIdent -> Alt -> CheckM ()
checkAlt mid (Alt _ cterm rhs) = withScope $ do
  checkConstrTerm mid  cterm
  insertConstrTerm False cterm
  checkRhs mid rhs
  idents' <-  returnUnrefVars
  when (not $ null idents') $ mapM_ genWarning' $ map unrefVar idents'

--
checkFieldExpression :: ModuleIdent -> Field Expression -> CheckM ()
checkFieldExpression mid (Field _ _ expr) = checkExpression mid expr -- Hier auch "visitId ident" ?

--
checkFieldPattern :: ModuleIdent -> Field ConstrTerm -> CheckM ()
checkFieldPattern mid (Field _ _ cterm) = checkConstrTerm mid  cterm

-- Check for idle and overlapping case alternatives
checkCaseAlternatives :: ModuleIdent -> [Alt] -> CheckM ()
checkCaseAlternatives mid alts = do
  checkIdleAlts mid alts
  checkOverlappingAlts mid alts

--
-- TODO FIXME this is buggy: is alts' required to be non-null or not? (hsi, bjp)
checkIdleAlts :: ModuleIdent -> [Alt] -> CheckM ()
checkIdleAlts _ alts = do
  alts' <- dropUnless' isVarAlt alts
  let idles         = tail_ [] alts'
      (Alt pos _ _) = head idles
  unless (null idles) $ genWarning pos idleCaseAlts
 where
  isVarAlt (Alt _ (VariablePattern ident) _)                = isVarId ident
  isVarAlt (Alt _ (ParenPattern (VariablePattern ident)) _) = isVarId ident
  isVarAlt (Alt _ (AsPattern _ (VariablePattern ident)) _)  = isVarId ident
  isVarAlt _ = return False

  -- safer versions of 'tail' and 'head'
  tail_ :: [a] -> [a] -> [a]
  tail_ alt []     = alt
  tail_ _   (_:xs) = xs

--
checkOverlappingAlts :: ModuleIdent -> [Alt] -> CheckM ()
checkOverlappingAlts _ [] = return ()
checkOverlappingAlts mid (alt : alts) = do
  (altsr, alts') <- partition' (equalAlts alt) alts
  mapM_ (\ (Alt pos _ _) -> genWarning pos overlappingCaseAlt) altsr
  checkOverlappingAlts mid alts'
  where
  equalAlts (Alt _ cterm1 _) (Alt _ cterm2 _) = equalConstrTerms cterm1 cterm2

  equalConstrTerms (LiteralPattern l1) (LiteralPattern l2)
    = return $ l1 == l2
  equalConstrTerms (NegativePattern id1 l1) (NegativePattern id2 l2)
    = return $ id1 == id2 && l1 == l2
  equalConstrTerms (VariablePattern id1) (VariablePattern id2) = do
    p <- isConsId id1
    return $ p && id1 == id2
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
  equalConstrTerms (TuplePattern _ cs1) (TuplePattern _ cs2)
    = equalConstrTerms (ConstructorPattern (qTupleId 2) cs1)
                       (ConstructorPattern (qTupleId 2) cs2)
  equalConstrTerms (ListPattern _ cs1) (ListPattern _ cs2)
    = cmpListM equalConstrTerms cs1 cs2
  equalConstrTerms (AsPattern _ cterm1) (AsPattern _ cterm2)
    = equalConstrTerms cterm1 cterm2
  equalConstrTerms (LazyPattern _ cterm1) (LazyPattern _ cterm2)
    = equalConstrTerms cterm1 cterm2
  equalConstrTerms _ _ = return False

  cmpListM :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m Bool
  cmpListM _ []     []     = return True
  cmpListM cmpM (x:xs) (y:ys) = do
    c <- cmpM x y
    if c then cmpListM cmpM xs ys
         else return False
  cmpListM _ _      _      = return False

-------------------------------------------------------------------------------
-- For detecting unreferenced variables, the following functions updates the
-- current check state by adding identifiers occuring in declaration left hand
-- sides.

--
insertDecl :: Decl -> CheckM ()
insertDecl (DataDecl _ ident _ cdecls) = do
  insertTypeConsId ident
  mapM_ insertConstrDecl cdecls
insertDecl (TypeDecl _ ident _ texpr) = do
  insertTypeConsId ident
  insertTypeExpr texpr
insertDecl (FunctionDecl _ ident _) = do
  c <- isConsId ident
  unless c $ insertVar ident
insertDecl (ExternalDecl _ _ _ ident _)
  = insertVar ident
insertDecl (FlatExternalDecl _ idents)
  = mapM_ insertVar idents
insertDecl (PatternDecl _ cterm _)
  = insertConstrTerm False cterm
insertDecl (ExtraVariables _ idents)
  = mapM_ insertVar idents
insertDecl _ = checked

--
insertTypeExpr :: TypeExpr -> CheckM ()
insertTypeExpr (VariableType _) = checked
insertTypeExpr (ConstructorType _ texprs)
  = mapM_ insertTypeExpr texprs
insertTypeExpr (TupleType texprs)
  = mapM_ insertTypeExpr texprs
insertTypeExpr (ListType texpr)
  = insertTypeExpr texpr
insertTypeExpr (ArrowType texpr1 texpr2)
  = mapM_ insertTypeExpr [texpr1,texpr2]
insertTypeExpr (RecordType _ restr) = do
  --mapM_ insertVar (concatMap fst fields)
  maybe (return ()) insertTypeExpr restr

--
insertConstrDecl :: ConstrDecl -> CheckM ()
insertConstrDecl (ConstrDecl _ _   ident _) = insertConsId ident
insertConstrDecl (ConOpDecl  _ _ _ ident _) = insertConsId ident

-- Notes:
--    - 'fp' indicates whether 'checkConstrTerm' deals with the arguments
--      of a function pattern or not.
--    - Since function patterns are not recognized before syntax check, it is
--      necessary to determine, whether a constructor pattern represents a
--      constructor or a function.
insertConstrTerm :: Bool -> ConstrTerm -> CheckM ()
insertConstrTerm fp (VariablePattern ident)
  | fp        = do
    c <- isConsId ident
    v <- isVarId ident
    unless c $ if name ident /= "_" && v then visitId ident else insertVar ident
  | otherwise = do
    c <- isConsId ident
    unless c $ insertVar ident
insertConstrTerm fp (ConstructorPattern qident cterms) = do
  c <- isQualConsId qident
  if c then mapM_ (insertConstrTerm fp) cterms
       else mapM_ (insertConstrTerm True) cterms
insertConstrTerm fp (InfixPattern cterm1 qident cterm2)
  = insertConstrTerm fp (ConstructorPattern qident [cterm1, cterm2])
insertConstrTerm fp (ParenPattern cterm)
  = insertConstrTerm fp cterm
insertConstrTerm fp (TuplePattern _ cterms)
  = mapM_ (insertConstrTerm fp) cterms
insertConstrTerm fp (ListPattern _ cterms)
  = mapM_ (insertConstrTerm fp) cterms
insertConstrTerm fp (AsPattern ident cterm) = do
  insertVar ident
  insertConstrTerm fp cterm
insertConstrTerm fp (LazyPattern _ cterm)
  = insertConstrTerm fp cterm
insertConstrTerm _ (FunctionPattern _ cterms)
  = mapM_ (insertConstrTerm True) cterms
insertConstrTerm _ (InfixFuncPattern cterm1 qident cterm2)
  = insertConstrTerm True (FunctionPattern qident [cterm1, cterm2])
insertConstrTerm fp (RecordPattern fields restr) = do
  mapM_ (insertFieldPattern fp) fields
  maybe (return ()) (insertConstrTerm fp) restr
insertConstrTerm _ _ = checked

--
insertFieldPattern :: Bool -> Field ConstrTerm -> CheckM ()
insertFieldPattern fp (Field _ _ cterm) = insertConstrTerm fp cterm

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

--
modifyScope :: (ScopeEnv.ScopeEnv QualIdent IdInfo -> ScopeEnv.ScopeEnv QualIdent IdInfo)
	       -> CState -> CState
modifyScope f state = state { scope = f $ scope state }

--
genWarning :: Position -> String -> CheckM ()
genWarning pos msg
  = modify (\state -> state{ messages = warnMsg:(messages state) })
 where warnMsg = Message (Just pos) msg

genWarning' :: (Position, String) -> CheckM ()
genWarning' = uncurry genWarning

--
insertVar :: Ident -> CheckM ()
insertVar ident
  | isAnnonId ident
  = return ()
  | otherwise
  = modify (modifyScope (ScopeEnv.insert (commonId ident) (VarInfo False)))

--
insertTypeVar :: Ident -> CheckM ()
insertTypeVar ident
  | isAnnonId ident
  = return ()
  | otherwise
  = modify (modifyScope (ScopeEnv.insert (typeId ident) (VarInfo False)))

--
insertConsId :: Ident -> CheckM ()
insertConsId ident
   = modify
       (\state -> modifyScope (ScopeEnv.insert (commonId ident) ConsInfo) state)

--
insertTypeConsId :: Ident -> CheckM ()
insertTypeConsId ident
   = modify
       (\state -> modifyScope (ScopeEnv.insert (typeId ident) ConsInfo) state)

--
isVarId :: Ident -> CheckM Bool
isVarId ident = gets (\state -> isVar state (commonId ident))

--
isConsId :: Ident -> CheckM Bool
isConsId ident = gets (\state -> isCons state (qualify ident))

--
isQualConsId :: QualIdent -> CheckM Bool
isQualConsId qid = gets (\state -> isCons state qid)

--
isShadowingVar :: Ident -> CheckM Bool
isShadowingVar ident = gets (\state -> isShadowing state (commonId ident))

--
visitId :: Ident -> CheckM ()
visitId ident = modify
  (modifyScope (ScopeEnv.modify visitVariable (commonId ident)))

--
visitTypeId :: Ident -> CheckM ()
visitTypeId ident = modify
  (modifyScope (ScopeEnv.modify visitVariable (typeId ident)))

--
isUnrefTypeVar :: Ident -> CheckM Bool
isUnrefTypeVar ident = gets (\state -> isUnref state (typeId ident))

--
returnUnrefVars :: CheckM [Ident]
returnUnrefVars = gets (\state ->
	   	    let ids    = map fst (ScopeEnv.toLevelList (scope state))
                        unrefs = filter (isUnref state) ids
	            in  map unqualify unrefs )

--
withScope :: CheckM a -> CheckM ()
withScope m = beginScope >> m >> endScope

--
beginScope :: CheckM ()
beginScope = modify (modifyScope ScopeEnv.beginScope)

--
endScope :: CheckM ()
endScope = modify (modifyScope ScopeEnv.endScopeUp)

--
dropUnless' :: (a -> CheckM Bool) -> [a] -> CheckM [a]
dropUnless' _ [] = return []
dropUnless' mpred (x:xs)
   = do p <- mpred x
	if p then return (x:xs) else dropUnless' mpred xs

--
partition' :: (a -> CheckM Bool) -> [a] -> CheckM ([a],[a])
partition' mpred xs' = part mpred [] [] xs'
 where
 part _ ts fs [] = return (reverse ts, reverse fs)
 part mpred' ts fs (x:xs)
   = do p <- mpred' x
	if p then part mpred' (x:ts) fs xs
	     else part mpred' ts (x:fs) xs

--
all' :: (a -> CheckM Bool) -> [a] -> CheckM Bool
all' _ [] = return True
all' mpred (x:xs)
   = do p <- mpred x
	if p then all' mpred xs else return False



-------------------------------------------------------------------------------

--
isShadowing :: CState -> QualIdent -> Bool
isShadowing state qid
   = let sc = scope state
     in  maybe False isVariable (ScopeEnv.lookup qid sc)
	 && ScopeEnv.level qid sc < ScopeEnv.currentLevel sc

--
isUnref :: CState -> QualIdent -> Bool
isUnref state qid
   = let sc = scope state
     in  maybe False (not . variableVisited) (ScopeEnv.lookup qid sc)
         && ScopeEnv.level qid sc == ScopeEnv.currentLevel sc

--
isVar :: CState -> QualIdent -> Bool
isVar state qid = maybe (isAnnonId (unqualify qid))
	           isVariable
		   (ScopeEnv.lookup qid (scope state))

--
isCons :: CState -> QualIdent -> Bool
isCons state qid = maybe (isImportedCons state qid)
		         isConstructor
			 (ScopeEnv.lookup qid (scope state))
 where
 isImportedCons state' qid'
    = case (qualLookupValue qid' (values state')) of
        (DataConstructor _ _):_    -> True
        (NewtypeConstructor _ _):_ -> True
        _                          -> False

--
isAnnonId :: Ident -> Bool
isAnnonId = (== anonId)

-- Since type identifiers and normal identifiers (e.g. functions, variables
-- or constructors) don't share the same namespace, it is necessary
-- to distinguish them in the scope environment of the check state.
-- For this reason type identifiers are annotated with 1 and normal
-- identifiers are annotated with 0.
--
commonId :: Ident -> QualIdent
commonId ident = qualify (unRenameIdent ident)

--
typeId :: Ident -> QualIdent
typeId ident = qualify (renameIdent ident 1)


-- ---------------------------------------------------------------------------
-- Warnings messages
-- ---------------------------------------------------------------------------

unrefTypeVar :: Ident -> (Position, String)
unrefTypeVar ident =
  (positionOfIdent ident,
   "unreferenced type variable \"" ++ show ident ++ "\"")

unrefVar :: Ident -> (Position, String)
unrefVar ident =
  (positionOfIdent ident,
   "unused declaration of variable \"" ++ show ident ++ "\"")

shadowingVar :: Ident -> (Position, String)
shadowingVar ident =
  (positionOfIdent ident,
   "shadowing symbol \"" ++ show ident ++ "\"")

idleCaseAlts :: String
idleCaseAlts = "idle case alternative(s)"

overlappingCaseAlt :: String
overlappingCaseAlt = "redundant overlapping case alternative"

rulesNotTogether :: Ident -> Position -> (Position, String)
rulesNotTogether ident pos
  = (positionOfIdent ident,
     "rules for function \"" ++ show ident ++ "\" "
     ++ "are not together "
     ++ "(first occurrence at "
     ++ show (line pos) ++ "." ++ show (column pos) ++ ")")

multiplyImportedModule :: ModuleIdent -> (Position, String)
multiplyImportedModule mid
  = (positionOfModuleIdent mid,
     "module \"" ++ show mid ++ "\" was imported more than once")

multiplyImportedSymbol :: ModuleIdent -> Ident -> (Position, String)
multiplyImportedSymbol mid ident
  = (positionOfIdent ident,
     "symbol \"" ++ show ident ++ "\" was imported from module \""
     ++ show mid ++ "\" more than once")

multiplyHiddenSymbol :: ModuleIdent -> Ident -> (Position, String)
multiplyHiddenSymbol mid ident
  = (positionOfIdent ident,
     "symbol \"" ++ show ident ++ "\" from module \"" ++ show mid
     ++ "\" was hidden more than once")
