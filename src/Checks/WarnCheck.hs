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

import Control.Monad.State
  (State, execState, filterM, gets, modify, unless, when, foldM_)
import qualified Data.Map as Map (empty, insert, lookup)
import Data.List (intersect, intersectBy, unionBy)
import Text.PrettyPrint

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.Messages (Message, posMessage)
import qualified Base.ScopeEnv as ScopeEnv

import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

-- Find potentially incorrect code in a Curry program and generate
-- the following warnings for:
--    - unreferenced variables
--    - shadowing variables
--    - idle case alternatives
--    - overlapping case alternatives
--    - function rules which are not together
warnCheck :: ValueEnv -> Module -> [Message]
warnCheck valEnv (Module mid es is ds) = runOn (initWcState mid valEnv) $ do
  checkExports es
  checkImports is
  mapM_ insertDecl ds
  mapM_ checkDecl ds
  checkFunctionRules ds


-- Current state of generating warnings
data WcState = WcState
  { moduleId    :: ModuleIdent
  , scope       :: ScopeEnv.ScopeEnv QualIdent IdInfo
  , valueEnv    :: ValueEnv
  , warnings    :: [Message]
  }

-- The monadic representation of the state allows the usage of monadic
-- syntax (do expression) for dealing easier and safer with its
-- contents.
type WCM = State WcState

initWcState :: ModuleIdent -> ValueEnv -> WcState
initWcState mid ve = WcState mid ScopeEnv.new ve []

getModuleIdent :: WCM ModuleIdent
getModuleIdent = gets moduleId

setModuleIdent :: ModuleIdent -> WCM ()
setModuleIdent mid = modify $ \ s -> s { moduleId = mid }

ok :: WCM ()
ok = return ()

--
report :: Message -> WCM ()
report warn = modify $ \ s -> s { warnings = warn : warnings s }

-- |Run a 'WCM' action and return the list of messages
runOn :: WcState -> WCM a -> [Message]
runOn s f = reverse $ warnings $ execState f s

-- ---------------------------------------------------------------------------
-- checkExports
-- ---------------------------------------------------------------------------

checkExports :: Maybe ExportSpec -> WCM ()
checkExports _ = ok -- TODO

-- ---------------------------------------------------------------------------
-- checkImports
-- ---------------------------------------------------------------------------

-- check import declarations for multiply imported modules and multiply
-- imported/hidden values.
--
-- The function uses a map of the already imported or hidden entities to
-- collect the entities throughout multiple import statements.
checkImports :: [ImportDecl] -> WCM ()
checkImports = foldM_ checkImport Map.empty
  where
  checkImport env (ImportDecl pos mid _ _ spec) = case Map.lookup mid env of
    Nothing   -> setImportSpec env mid $ fromImpSpec spec
    Just ishs -> checkImportSpec env pos mid ishs spec

  checkImportSpec env _ mid (_, _)    Nothing = do
    report $ warnMultiplyImportedModule mid
    return env

  checkImportSpec env _ mid (is, hs) (Just (Importing _ is'))
    | null is && any (`notElem` hs) is' = do
        report $ warnMultiplyImportedModule mid
        setImportSpec env mid (is', hs)
    | null iis  = setImportSpec env mid (is' ++ is, hs)
    | otherwise = do
        mapM_ (report . (warnMultiplyImportedSymbol mid) . impName) iis
        setImportSpec env mid (unionBy cmpImport is' is, hs)
    where iis = intersectBy cmpImport is' is

  checkImportSpec env _ mid (is, hs) (Just (Hiding _ hs'))
    | null ihs  = setImportSpec env mid (is, hs' ++ hs)
    | otherwise = do
        mapM_ (report . (warnMultiplyHiddenSymbol mid) . impName) ihs
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
-- checkFunctionRules
-- ---------------------------------------------------------------------------

-- Find function rules which are not together
checkFunctionRules :: [Decl] -> WCM ()
checkFunctionRules decls = foldM_ checkDO (mkIdent "", Map.empty) decls
  where
  checkDO (prevId, env) (FunctionDecl pos ident _) = do
    c <- isConsId ident
    if c || prevId == ident
      then return (ident, env)
      else case Map.lookup ident env of
        Nothing   -> return (ident, Map.insert ident pos env)
        Just pos' -> do
          report $ warnDisjoinedFunctionRules ident pos'
          return (ident, env)
  checkDO (_, env) _ = return (mkIdent "", env)

-- ---------------------------------------------------------------------------
-- do something else
-- ---------------------------------------------------------------------------

--
checkDecl :: Decl -> WCM ()
checkDecl (DataDecl   _ _ vs cs) = withScope $ do
  mapM_ insertTypeVar vs
  mapM_ checkConstrDecl cs
  vs' <- filterM isUnrefTypeVar vs
  unless (null vs') $ mapM_ report $ map unrefTypeVar vs'
checkDecl (TypeDecl   _ _ vs ty) = withScope $ do
  mapM_ insertTypeVar vs
  checkTypeExpr ty
  vs' <- filterM isUnrefTypeVar vs
  unless (null vs') $ mapM_ report $ map unrefTypeVar vs'
checkDecl (FunctionDecl _ _ eqs) = withScope $ mapM_ checkEquation eqs
checkDecl (PatternDecl  _ p rhs) = do
  checkConstrTerm p
  checkRhs rhs
checkDecl _ = ok

-- Checks locally declared identifiers (i.e. functions and logic variables)
-- for shadowing
checkLocalDecl :: Decl -> WCM ()
checkLocalDecl (FunctionDecl  _ f _) = checkShadowing f
checkLocalDecl (ExtraVariables _ vs) = mapM_ checkShadowing vs
checkLocalDecl (PatternDecl   _ p _) = do
  mid <- getModuleIdent
  setModuleIdent (mkMIdent []) -- TODO: is this right?
  checkConstrTerm p
  setModuleIdent mid
checkLocalDecl _ = ok

--
checkConstrDecl :: ConstrDecl -> WCM ()
checkConstrDecl (ConstrDecl     _ _ c tys) = do
  visitId c
  mapM_ checkTypeExpr tys
checkConstrDecl (ConOpDecl _ _ ty1 op ty2) = do
  visitId op
  checkTypeExpr ty1
  checkTypeExpr ty2


checkTypeExpr :: TypeExpr -> WCM ()
checkTypeExpr (ConstructorType qid texprs) = do
  mid <- getModuleIdent
  maybe ok visitTypeId (localIdent mid qid)
  mapM_ checkTypeExpr texprs
checkTypeExpr (VariableType ident)
  = visitTypeId ident
checkTypeExpr (TupleType texprs)
  = mapM_ checkTypeExpr texprs
checkTypeExpr (ListType texpr)
  = checkTypeExpr texpr
checkTypeExpr (ArrowType texpr1 texpr2) = do
  checkTypeExpr texpr1
  checkTypeExpr texpr2
checkTypeExpr (RecordType fields restr) = do
  mapM_ checkTypeExpr (map snd fields)
  maybe ok checkTypeExpr restr

-- Check an equation for warnings.
-- This is done in a seperate scope as the left-hand-side may introduce
-- new variables.
checkEquation :: Equation -> WCM ()
checkEquation (Equation _ lhs rhs) = withScope $
  checkLhs lhs >> checkRhs rhs >> reportUnusedVars

--
checkLhs :: Lhs -> WCM ()
checkLhs (FunLhs    f ts) = do
  visitId f
  mapM_ checkConstrTerm ts
  mapM_ (insertConstrTerm False) ts
checkLhs (OpLhs t1 op t2) = checkLhs (FunLhs op [t1, t2])
checkLhs (ApLhs   lhs ts) = do
  checkLhs lhs
  mapM_ checkConstrTerm ts
  mapM_ (insertConstrTerm False) ts

-- Check the right-hand-side of an equation.
-- Because local declarations may introduce new variables, we need
-- another scope nesting.
checkRhs :: Rhs -> WCM ()
checkRhs (SimpleRhs _ expr ds) = withScope $ do
  mapM_ checkLocalDecl ds
  mapM_ insertDecl ds
  mapM_ checkDecl ds
  checkFunctionRules ds
  checkExpression expr
  reportUnusedVars
checkRhs (GuardedRhs cexprs ds) = withScope $ do
  mapM_ checkLocalDecl ds
  mapM_ insertDecl ds
  mapM_ checkDecl ds
  checkFunctionRules ds
  mapM_ checkCondExpr cexprs
  reportUnusedVars

--
checkCondExpr :: CondExpr -> WCM ()
checkCondExpr (CondExpr _ c e) = checkExpression c >> checkExpression e

--
checkConstrTerm :: ConstrTerm -> WCM ()
checkConstrTerm (VariablePattern v) = checkShadowing v
checkConstrTerm (ConstructorPattern _ cterms)
  = mapM_ checkConstrTerm cterms
checkConstrTerm (InfixPattern cterm1 qident cterm2)
  = checkConstrTerm (ConstructorPattern qident [cterm1, cterm2])
checkConstrTerm (ParenPattern cterm)
  = checkConstrTerm cterm
checkConstrTerm (TuplePattern _ cterms)
  = mapM_ checkConstrTerm cterms
checkConstrTerm (ListPattern _ cterms)
  = mapM_ checkConstrTerm cterms
checkConstrTerm (AsPattern v cterm) = do
  checkShadowing v
  checkConstrTerm cterm
checkConstrTerm (LazyPattern _ cterm)
  = checkConstrTerm cterm
checkConstrTerm (FunctionPattern _ cterms)
  = mapM_ checkConstrTerm cterms
checkConstrTerm  (InfixFuncPattern cterm1 qident cterm2)
  = checkConstrTerm  (FunctionPattern qident [cterm1, cterm2])
checkConstrTerm  (RecordPattern fields restr) = do
  mapM_ checkFieldPattern fields
  maybe ok checkConstrTerm restr
checkConstrTerm _ = return ()

--
checkExpression :: Expression -> WCM ()
checkExpression (Variable qident) = do
  mid <- getModuleIdent
  maybe ok visitId (localIdent mid qident)
checkExpression (Paren expr)
  = checkExpression expr
checkExpression (Typed expr _)
  = checkExpression expr
checkExpression (Tuple _ exprs)
  = mapM_ checkExpression exprs
checkExpression (List _ exprs)
  = mapM_ checkExpression exprs
checkExpression (ListCompr _ expr stmts) = withScope $ do
  mapM_ checkStatement stmts
  checkExpression expr
  reportUnusedVars
checkExpression (EnumFrom expr)
  = checkExpression expr
checkExpression (EnumFromThen expr1 expr2)
  = mapM_ checkExpression [expr1, expr2]
checkExpression (EnumFromTo expr1 expr2)
  = mapM_ checkExpression [expr1, expr2]
checkExpression (EnumFromThenTo expr1 expr2 expr3)
  = mapM_ checkExpression [expr1, expr2, expr3]
checkExpression (UnaryMinus _ expr)
  = checkExpression expr
checkExpression (Apply expr1 expr2)
  = mapM_ checkExpression [expr1, expr2]
checkExpression (InfixApply expr1 op expr2) = do
  mid <- getModuleIdent
  maybe ok visitId (localIdent mid (opName op))
  mapM_ checkExpression [expr1, expr2]
checkExpression (LeftSection expr _)
  = checkExpression expr
checkExpression (RightSection _ expr)
  = checkExpression expr
checkExpression (Lambda _ cterms expr) = withScope $ do
  mapM_ checkConstrTerm cterms
  mapM_ (insertConstrTerm False) cterms
  checkExpression expr
  reportUnusedVars
checkExpression (Let decls expr) = withScope $ do
  mapM_ checkLocalDecl decls
  mapM_ insertDecl decls
  mapM_ checkDecl decls
  checkFunctionRules decls
  checkExpression expr
  reportUnusedVars
checkExpression (Do stmts expr) = withScope $ do
  mapM_ checkStatement stmts
  checkExpression expr
  reportUnusedVars
checkExpression (IfThenElse _ expr1 expr2 expr3)
  = mapM_ checkExpression [expr1, expr2, expr3]
checkExpression (Case _ expr alts) = do
  checkExpression expr
  mapM_ checkAlt alts
  checkCaseAlternatives alts
checkExpression (RecordConstr fields)
  = mapM_ checkFieldExpression fields
checkExpression (RecordSelection expr _)
  = checkExpression expr -- Hier auch "visitId ident" ?
checkExpression (RecordUpdate fields expr) = do
  mapM_ checkFieldExpression fields
  checkExpression expr
checkExpression _  = ok

--
checkStatement :: Statement -> WCM ()
checkStatement (StmtExpr _ expr) = checkExpression expr
checkStatement (StmtDecl  decls) = do
  mapM_ checkLocalDecl decls
  mapM_ insertDecl decls
  mapM_ checkDecl decls
  checkFunctionRules decls
checkStatement (StmtBind _ cterm expr) = do
  checkConstrTerm cterm
  insertConstrTerm False cterm
  checkExpression expr

--
checkAlt :: Alt -> WCM ()
checkAlt (Alt _ cterm rhs) = withScope $ do
  checkConstrTerm  cterm
  insertConstrTerm False cterm
  checkRhs rhs
  reportUnusedVars

--
checkFieldExpression :: Field Expression -> WCM ()
checkFieldExpression (Field _ _ expr) = checkExpression expr -- Hier auch "visitId ident" ?

--
checkFieldPattern :: Field ConstrTerm -> WCM ()
checkFieldPattern (Field _ _ cterm) = checkConstrTerm cterm

-- Check for idle and overlapping case alternatives
checkCaseAlternatives :: [Alt] -> WCM ()
checkCaseAlternatives alts = do
  checkIdleAlts alts
  checkOverlappingAlts alts

--
-- TODO FIXME this is buggy: is alts' required to be non-null or not? (hsi, bjp)
checkIdleAlts :: [Alt] -> WCM ()
checkIdleAlts alts = do
  alts' <- dropUnless' isVarAlt alts
  let idles         = tail_ [] alts'
      (Alt pos _ _) = head idles
  unless (null idles) $ report $ idleCaseAlts pos
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
checkOverlappingAlts :: [Alt] -> WCM ()
checkOverlappingAlts [] = return ()
checkOverlappingAlts (alt : alts) = do
  (altsr, alts') <- partition' (equalAlts alt) alts
  mapM_ (\ (Alt pos _ _) -> report $ overlappingCaseAlt pos) altsr
  checkOverlappingAlts alts'
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

checkShadowing :: Ident -> WCM ()
checkShadowing x = do
  s <- isShadowingVar x
  when s $ report $ shadowingVar x

reportUnusedVars :: WCM ()
reportUnusedVars = do
  unused <- returnUnrefVars
  unless (null unused) $ mapM_ report $ map unrefVar unused

-------------------------------------------------------------------------------
-- For detecting unreferenced variables, the following functions updates the
-- current check state by adding identifiers occuring in declaration left hand
-- sides.

--
insertDecl :: Decl -> WCM ()
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
insertDecl _ = ok

--
insertTypeExpr :: TypeExpr -> WCM ()
insertTypeExpr (VariableType _) = ok
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
insertConstrDecl :: ConstrDecl -> WCM ()
insertConstrDecl (ConstrDecl _ _   ident _) = insertConsId ident
insertConstrDecl (ConOpDecl  _ _ _ ident _) = insertConsId ident

-- Notes:
--    - 'fp' indicates whether 'checkConstrTerm' deals with the arguments
--      of a function pattern or not.
--    - Since function patterns are not recognized before syntax check, it is
--      necessary to determine, whether a constructor pattern represents a
--      constructor or a function.
insertConstrTerm :: Bool -> ConstrTerm -> WCM ()
insertConstrTerm fp (VariablePattern v)
  | fp        = do
    c <- isConsId v
    var <- isVarId v
    unless c $ if idName v /= "_" && var then visitId v else insertVar v
  | otherwise = do
    c <- isConsId v
    unless c $ insertVar v
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
insertConstrTerm _ _ = ok

--
insertFieldPattern :: Bool -> Field ConstrTerm -> WCM ()
insertFieldPattern fp (Field _ _ cterm) = insertConstrTerm fp cterm

-- ---------------------------------------------------------------------------

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
	       -> WcState -> WcState
modifyScope f state = state { scope = f $ scope state }

insertScope :: QualIdent -> IdInfo -> WCM ()
insertScope qid info = modify $ modifyScope $ ScopeEnv.insert qid info

--
insertVar :: Ident -> WCM ()
insertVar ident
  | isAnonId ident = return ()
  | otherwise      = insertScope (commonId ident) (VarInfo False)

--
insertTypeVar :: Ident -> WCM ()
insertTypeVar ident
  | isAnonId ident = return ()
  | otherwise      = insertScope (typeId ident) (VarInfo False)

--
insertConsId :: Ident -> WCM ()
insertConsId ident = insertScope (commonId ident) ConsInfo

--
insertTypeConsId :: Ident -> WCM ()
insertTypeConsId ident = insertScope (typeId ident) ConsInfo

--
isVarId :: Ident -> WCM Bool
isVarId ident = gets (\s -> isVar s (commonId ident))

--
isConsId :: Ident -> WCM Bool
isConsId ident = gets (\s -> isCons s (qualify ident))

--
isQualConsId :: QualIdent -> WCM Bool
isQualConsId qid = gets (\s -> isCons s qid)

--
isShadowingVar :: Ident -> WCM Bool
isShadowingVar ident = gets (\s -> isShadowing s (commonId ident))

--
visitId :: Ident -> WCM ()
visitId ident = modify
  (modifyScope (ScopeEnv.modify visitVariable (commonId ident)))

--
visitTypeId :: Ident -> WCM ()
visitTypeId ident = modify
  (modifyScope (ScopeEnv.modify visitVariable (typeId ident)))

--
isUnrefTypeVar :: Ident -> WCM Bool
isUnrefTypeVar ident = gets (\s -> isUnref s (typeId ident))

--
returnUnrefVars :: WCM [Ident]
returnUnrefVars = gets (\s ->
	   	    let ids    = map fst (ScopeEnv.toLevelList (scope s))
                        unrefs = filter (isUnref s) ids
	            in  map unqualify unrefs )

--
withScope :: WCM a -> WCM ()
withScope m = beginScope >> m >> endScope

--
beginScope :: WCM ()
beginScope = modify $ modifyScope ScopeEnv.beginScope

--
endScope :: WCM ()
endScope = modify $ modifyScope ScopeEnv.endScopeUp

--
dropUnless' :: Monad m => (a -> m Bool) -> [a] -> m [a]
dropUnless' _     []     = return []
dropUnless' mpred (x:xs) = do
  p <- mpred x
  if p then return (x:xs) else dropUnless' mpred xs

--
partition' :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partition' mpred xs' = part mpred [] [] xs'
 where
 part _      ts fs []     = return (reverse ts, reverse fs)
 part mpred' ts fs (x:xs) = do
  p <- mpred' x
  if p then part mpred' (x:ts) fs     xs
       else part mpred' ts     (x:fs) xs

--
all' :: Monad m => (a -> m Bool) -> [a] -> m Bool
all' _     []     = return True
all' mpred (x:xs) = do
  p <- mpred x
  if p then all' mpred xs else return False

------------------------------------------------------------------------------

--
isShadowing :: WcState -> QualIdent -> Bool
isShadowing state qid
   = let sc = scope state
     in  maybe False isVariable (ScopeEnv.lookup qid sc)
     && ScopeEnv.level qid sc < ScopeEnv.currentLevel sc

--
isUnref :: WcState -> QualIdent -> Bool
isUnref state qid
   = let sc = scope state
     in  maybe False (not . variableVisited) (ScopeEnv.lookup qid sc)
         && ScopeEnv.level qid sc == ScopeEnv.currentLevel sc

--
isVar :: WcState -> QualIdent -> Bool
isVar state qid = maybe (isAnonId (unqualify qid))
                  isVariable
                  (ScopeEnv.lookup qid (scope state))

--
isCons :: WcState -> QualIdent -> Bool
isCons state qid = maybe (isImportedCons state qid)
                   isConstructor
                   (ScopeEnv.lookup qid (scope state))
 where
 isImportedCons state' qid'
    = case (qualLookupValue qid' (valueEnv state')) of
        (DataConstructor  _ _ _) : _ -> True
        (NewtypeConstructor _ _) : _ -> True
        _                            -> False

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

warnMultiplyImportedModule :: ModuleIdent -> Message
warnMultiplyImportedModule mid = posMessage mid $ hsep $ map text
  ["Module", moduleName mid, "is imported more than once"]

warnMultiplyImportedSymbol :: ModuleIdent -> Ident -> Message
warnMultiplyImportedSymbol mid ident = posMessage ident $ hsep $ map text
  [ "Symbol", escName ident, "from module", moduleName mid
  , "is imported more than once" ]

warnMultiplyHiddenSymbol :: ModuleIdent -> Ident -> Message
warnMultiplyHiddenSymbol mid ident = posMessage ident $ hsep $ map text
  [ "Symbol", escName ident, "from module", moduleName mid
  , "is hidden more than once" ]

warnDisjoinedFunctionRules :: Ident -> Position -> Message
warnDisjoinedFunctionRules ident pos = posMessage ident $ hsep (map text
  [ "Rules for function", escName ident, "are disjoined" ])
  <+> parens (text "first occurrence at" <+> text (showLine pos))

unrefTypeVar :: Ident -> Message
unrefTypeVar ident = posMessage ident $ hsep $ map text
  [ "Unreferenced type variable", escName ident ]

unrefVar :: Ident -> Message
unrefVar ident = posMessage ident $ hsep $ map text
  [ "Unused declaration of variable", escName ident ]

shadowingVar :: Ident -> Message
shadowingVar ident = posMessage ident $ hsep $ map text
  [ "Shadowing symbol", escName ident ]

idleCaseAlts :: Position -> Message
idleCaseAlts p = posMessage p $ text "Idle case alternative(s)"

overlappingCaseAlt :: Position -> Message
overlappingCaseAlt p = posMessage p $ text
  "Redundant overlapping case alternative"
