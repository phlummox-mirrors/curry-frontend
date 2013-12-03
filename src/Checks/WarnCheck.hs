{- |
    Module      :  $Header$
    Description :  Checks for irregular code
    Copyright   :  (c) 2006        Martin Engelke
                       2011 - 2012 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module searches for potentially irregular code and generates
    warning messages.
-}
module Checks.WarnCheck (warnCheck) where

import           Control.Monad
  (filterM, foldM_, guard, liftM, when, unless)
import           Control.Monad.State.Strict (State, execState, gets, modify)
import qualified Data.Map            as Map (empty, insert, lookup)
import           Data.Maybe                 (catMaybes, isJust)
import           Data.List
  (intersect, intersectBy, nub, partition, sort, unionBy)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty (ppPattern, ppExpr, ppIdent)

import Base.Messages (Message, posMessage, internalError)
import qualified Base.ScopeEnv as SE
  ( ScopeEnv, new, beginScope, endScopeUp, insert, lookup, level, modify
  , lookupWithLevel, toLevelList, currentLevel)

import Base.Types
import Env.TypeConstructor (TCEnv, TypeInfo (..), lookupTC, qualLookupTC)
import Env.Value (ValueEnv, ValueInfo (..), qualLookupValue)

import CompilerOpts

-- Find potentially incorrect code in a Curry program and generate warnings
-- for the following issues:
--   - multiply imported modules, multiply imported/hidden values
--   - unreferenced variables
--   - shadowing variables
--   - idle case alternatives
--   - overlapping case alternatives
--   - non-adjacent function rules
warnCheck :: Options -> ValueEnv -> TCEnv -> Module -> [Message]
warnCheck opts valEnv tcEnv (Module _ mid es is ds)
  = runOn (initWcState mid valEnv tcEnv (optWarnFlags opts)) $ do
      checkExports   es
      checkImports   is
      checkDeclGroup ds

type ScopeEnv = SE.ScopeEnv QualIdent IdInfo

-- Current state of generating warnings
data WcState = WcState
  { moduleId    :: ModuleIdent
  , scope       :: ScopeEnv
  , valueEnv    :: ValueEnv
  , tyConsEnv   :: TCEnv
  , warnFlags   :: [WarnFlag]
  , warnings    :: [Message]
  }

-- The monadic representation of the state allows the usage of monadic
-- syntax (do expression) for dealing easier and safer with its
-- contents.
type WCM = State WcState

initWcState :: ModuleIdent -> ValueEnv -> TCEnv -> [WarnFlag] -> WcState
initWcState mid ve te wf = WcState mid SE.new ve te wf []

getModuleIdent :: WCM ModuleIdent
getModuleIdent = gets moduleId

modifyScope :: (ScopeEnv -> ScopeEnv) -> WCM ()
modifyScope f = modify $ \s -> s { scope = f $ scope s }

warnFor :: WarnFlag -> WCM () -> WCM ()
warnFor f act = do
  warn <- gets $ \s -> f `elem` warnFlags s
  when warn act

report :: Message -> WCM ()
report w = modify $ \ s -> s { warnings = w : warnings s }

ok :: WCM ()
ok = return ()

-- |Run a 'WCM' action and return the list of messages
runOn :: WcState -> WCM a -> [Message]
runOn s f = sort $ warnings $ execState f s

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
checkImports = warnFor WarnMultipleImports . foldM_ checkImport Map.empty
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

  impName (Import           v) = v
  impName (ImportTypeAll    t) = t
  impName (ImportTypeWith t _) = t

-- ---------------------------------------------------------------------------
-- checkDeclGroup
-- ---------------------------------------------------------------------------

checkDeclGroup :: [Decl] -> WCM ()
checkDeclGroup ds = do
  mapM_ insertDecl   ds
  mapM_ checkDecl    ds
  checkRuleAdjacency ds

-- Find function rules which are not together
checkRuleAdjacency :: [Decl] -> WCM ()
checkRuleAdjacency decls = warnFor WarnDisjoinedRules
                         $ foldM_ check (mkIdent "", Map.empty) decls
  where
  check (prevId, env) (FunctionDecl p f _) = do
    cons <- isConsId f
    if cons || prevId == f
      then return (f, env)
      else case Map.lookup f env of
        Nothing -> return (f, Map.insert f p env)
        Just p' -> do
          report $ warnDisjoinedFunctionRules f p'
          return (f, env)
  check (_    , env) _                     = return (mkIdent "", env)

checkLocalDeclGroup :: [Decl] -> WCM ()
checkLocalDeclGroup ds = do
  mapM_ checkLocalDecl ds
  checkDeclGroup       ds

checkDecl :: Decl -> WCM ()
checkDecl (DataDecl   _ _ vs cs) = inNestedScope $ do
  mapM_ insertTypeVar   vs
  mapM_ checkConstrDecl cs
  reportUnusedTypeVars  vs
checkDecl (TypeDecl   _ _ vs ty) = inNestedScope $ do
  mapM_ insertTypeVar  vs
  checkTypeExpr ty
  reportUnusedTypeVars vs
checkDecl (FunctionDecl p f eqs) = checkFunctionDecl p f eqs
checkDecl (PatternDecl  _ p rhs) = checkPattern p >> checkRhs rhs
checkDecl _                      = ok

checkConstrDecl :: ConstrDecl -> WCM ()
checkConstrDecl (ConstrDecl     _ _ c tys) = do
  visitId c
  mapM_ checkTypeExpr tys
checkConstrDecl (ConOpDecl _ _ ty1 op ty2) = do
  visitId op
  mapM_ checkTypeExpr [ty1, ty2]

checkTypeExpr :: TypeExpr -> WCM ()
checkTypeExpr (ConstructorType qid tys) = do
  visitQTypeId qid
  mapM_ checkTypeExpr tys
checkTypeExpr (VariableType          v) = visitTypeId v
checkTypeExpr (TupleType           tys) = mapM_ checkTypeExpr tys
checkTypeExpr (ListType             ty) = checkTypeExpr ty
checkTypeExpr (ArrowType       ty1 ty2) = mapM_ checkTypeExpr [ty1, ty2]
checkTypeExpr (RecordType       fs rty) = do
  mapM_ checkTypeExpr (map snd fs)
  maybe ok checkTypeExpr rty

-- Checks locally declared identifiers (i.e. functions and logic variables)
-- for shadowing
checkLocalDecl :: Decl -> WCM ()
checkLocalDecl (FunctionDecl _ f _) = checkShadowing f
checkLocalDecl (FreeDecl      _ vs) = mapM_ checkShadowing vs
checkLocalDecl (PatternDecl  _ p _) = checkPattern p
checkLocalDecl _                    = ok

checkFunctionDecl :: Position -> Ident -> [Equation] -> WCM ()
checkFunctionDecl _ _ []  = ok
checkFunctionDecl p f eqs = inNestedScope $ do
  mapM_ checkEquation eqs
  checkNonExhaustivePattern ("an equation for " ++ escName f) p
    $ map (\(Equation _ lhs _) -> snd (flatLhs lhs)) eqs

-- Check an equation for warnings.
-- This is done in a seperate scope as the left-hand-side may introduce
-- new variables.
checkEquation :: Equation -> WCM ()
checkEquation (Equation _ lhs rhs) = inNestedScope $ do
  checkLhs lhs
  checkRhs rhs
  reportUnusedVars

checkLhs :: Lhs -> WCM ()
checkLhs (FunLhs    f ts) = do
  visitId f
  mapM_ checkPattern ts
  mapM_ (insertPattern False) ts
checkLhs (OpLhs t1 op t2) = checkLhs (FunLhs op [t1, t2])
checkLhs (ApLhs   lhs ts) = do
  checkLhs lhs
  mapM_ checkPattern ts
  mapM_ (insertPattern False) ts

checkPattern :: Pattern -> WCM ()
checkPattern (VariablePattern        v) = checkShadowing v
checkPattern (ConstructorPattern  _ ps) = mapM_ checkPattern ps
checkPattern (InfixPattern     p1 f p2)
  = checkPattern (ConstructorPattern f [p1, p2])
checkPattern (ParenPattern           p) = checkPattern p
checkPattern (TuplePattern        _ ps) = mapM_ checkPattern ps
checkPattern (ListPattern         _ ps) = mapM_ checkPattern ps
checkPattern (AsPattern            v p) = checkShadowing v >> checkPattern p
checkPattern (LazyPattern          _ p) = checkPattern p
checkPattern (FunctionPattern     _ ps) = mapM_ checkPattern ps
checkPattern (InfixFuncPattern p1 f p2)
  = checkPattern (FunctionPattern f [p1, p2])
checkPattern  (RecordPattern      fs r) = do
  mapM_ (\ (Field _ _ p) -> checkPattern p) fs
  maybe ok checkPattern r
checkPattern _                          = ok

-- Check the right-hand-side of an equation.
-- Because local declarations may introduce new variables, we need
-- another scope nesting.
checkRhs :: Rhs -> WCM ()
checkRhs (SimpleRhs _ e ds) = inNestedScope $ do
  checkLocalDeclGroup ds
  checkExpr e
  reportUnusedVars
checkRhs (GuardedRhs ce ds) = inNestedScope $ do
  checkLocalDeclGroup ds
  mapM_ checkCondExpr ce
  reportUnusedVars

checkCondExpr :: CondExpr -> WCM ()
checkCondExpr (CondExpr _ c e) = checkExpr c >> checkExpr e

checkExpr :: Expression -> WCM ()
checkExpr (Variable              v) = visitQId v
checkExpr (Paren                 e) = checkExpr e
checkExpr (Typed               e _) = checkExpr e
checkExpr (Tuple              _ es) = mapM_ checkExpr es
checkExpr (List               _ es) = mapM_ checkExpr es
checkExpr (ListCompr       _ e sts) = checkStatements sts e
checkExpr (EnumFrom              e) = checkExpr e
checkExpr (EnumFromThen      e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (EnumFromTo        e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (EnumFromThenTo e1 e2 e3) = mapM_ checkExpr [e1, e2, e3]
checkExpr (UnaryMinus          _ e) = checkExpr e
checkExpr (Apply             e1 e2) = mapM_ checkExpr [e1, e2]
checkExpr (InfixApply     e1 op e2) = do
  visitQId (opName op)
  mapM_ checkExpr [e1, e2]
checkExpr (LeftSection         e _) = checkExpr e
checkExpr (RightSection        _ e) = checkExpr e
checkExpr (Lambda           _ ps e) = inNestedScope $ do
  mapM_ checkPattern ps
  mapM_ (insertPattern False) ps
  checkExpr e
  reportUnusedVars
checkExpr (Let                ds e) = inNestedScope $ do
  checkLocalDeclGroup ds
  checkExpr e
  reportUnusedVars
checkExpr (Do                sts e) = checkStatements sts e
checkExpr (IfThenElse   _ e1 e2 e3) = mapM_ checkExpr [e1, e2, e3]
checkExpr (Case        _ ct e alts) = do
  checkExpr e
  mapM_ checkAlt alts
  checkCaseAlternatives ct alts
checkExpr (RecordConstr         fs) = mapM_ checkFieldExpression fs
checkExpr (RecordSelection     e _) = checkExpr e -- Hier auch "visitId ident" ?
checkExpr (RecordUpdate       fs e) = do
  mapM_ checkFieldExpression fs
  checkExpr e
checkExpr _                       = ok

checkStatements :: [Statement] -> Expression -> WCM ()
checkStatements []     e = checkExpr e
checkStatements (s:ss) e = inNestedScope $ do
  checkStatement s >> checkStatements ss e
  reportUnusedVars

checkStatement :: Statement -> WCM ()
checkStatement (StmtExpr   _ e) = checkExpr e
checkStatement (StmtDecl    ds) = checkLocalDeclGroup ds
checkStatement (StmtBind _ p e) = do
  checkPattern p >> insertPattern False p
  checkExpr e

checkAlt :: Alt -> WCM ()
checkAlt (Alt _ p rhs) = inNestedScope $ do
  checkPattern p >> insertPattern False p
  checkRhs rhs
  reportUnusedVars

checkFieldExpression :: Field Expression -> WCM ()
checkFieldExpression (Field _ _ e) = checkExpr e -- Hier auch "visitId ident" ?

-- Check for idle and overlapping case alternatives
checkCaseAlternatives :: CaseType -> [Alt] -> WCM ()
checkCaseAlternatives _  []                     = ok
checkCaseAlternatives ct alts@(Alt pos _ _ : _) = do
  checkIdleAlts alts
  when (ct == Flex) (checkOverlappingAlts alts)
  checkNonExhaustivePattern "a case alternative" pos
    (map (\(Alt _ p _) -> [p]) alts)

checkIdleAlts :: [Alt] -> WCM ()
checkIdleAlts alts = warnFor WarnIdleAlternatives $ case idles of
  Alt p _ _ : _ : _ -> report $ warnIdleCaseAlts p
  _                 -> ok
  where
  idles = dropWhile (not . isVarAlt) alts

  isVarAlt (Alt _ p _) = isVarPat' p

  isVarPat' (VariablePattern _) = True
  isVarPat' (ParenPattern    p) = isVarPat' p
  isVarPat' (AsPattern     _ p) = isVarPat' p
  isVarPat' _                   = False

checkOverlappingAlts :: [Alt] -> WCM ()
checkOverlappingAlts []           = ok
checkOverlappingAlts (alt : alts) = warnFor WarnOverlapping $ do
  let (overlapped, rest) = partition (eqAlt alt) alts
  unless (null overlapped) $ report $ warnOverlappingCaseAlts (alt : overlapped)
  checkOverlappingAlts rest
  where
  eqAlt (Alt _ p1 _) (Alt _ p2 _) = eqPattern p1 p2

  eqPattern (LiteralPattern         l1) (LiteralPattern         l2)
    = l1 == l2
  eqPattern (NegativePattern    id1 l1) (NegativePattern    id2 l2)
    = id1 == id2 && l1 == l2
  eqPattern (VariablePattern         _) (VariablePattern         _)
    = False -- treated as idle case alternative!
  eqPattern (ConstructorPattern c1 cs1) (ConstructorPattern c2 cs2)
    = and ((c1 == c2) : zipWith eqPattern cs1 cs2)
  eqPattern (InfixPattern     l1 c1 r1) (InfixPattern     l2 c2 r2)
    = and [c1 == c2, l1 `eqPattern` l2, r1 `eqPattern` r2]
  eqPattern (ParenPattern           p1) (ParenPattern           p2)
    = eqPattern p1 p2
  eqPattern (TuplePattern         _ p1) (TuplePattern         _ p2)
    = and (zipWith eqPattern p1 p2)
  eqPattern (ListPattern          _ p1) (ListPattern          _ p2)
    = and (zipWith eqPattern p1 p2)
  eqPattern (AsPattern            _ p1) (AsPattern            _ p2)
    = eqPattern p1 p2
  eqPattern (LazyPattern          _ p1) (LazyPattern          _ p2)
    = eqPattern p1 p2
  eqPattern _                           _
    = False

-- -----------------------------------------------------------------------------
-- Check for non-exhaustive patterns
-- -----------------------------------------------------------------------------

checkNonExhaustivePattern :: String -> Position -> [[Pattern]] -> WCM ()
checkNonExhaustivePattern loc pos pats = warnFor WarnIncompletePatterns $ do
  missing <- missingPattern (map (map simplifyPat) pats)
  unless (null missing) $ report $ warnMissingPattern loc pos $
    tidyExhaustivePats missing

tidyExhaustivePats :: [ExhaustivePats] -> [ExhaustivePats]
tidyExhaustivePats = map (\(xs, ys) -> (map tidyPat xs, ys))

-- simplify pattern to only consist of
--   * variables
--   * literals
--   * constructors
--   * record pattern (currently ignored)
simplifyPat :: Pattern -> Pattern
simplifyPat l@(LiteralPattern      _) = l
simplifyPat (NegativePattern     _ l) = LiteralPattern (negateLit l)
  where
  negateLit (Int   i n) = Int   i (-n)
  negateLit (Float r d) = Float r (-d)
  negateLit x           = x
simplifyPat v@(VariablePattern     _) = v
simplifyPat (ConstructorPattern c ps)
  = ConstructorPattern c (map simplifyPat ps)
simplifyPat (InfixPattern    p1 c p2)
  = ConstructorPattern c (map simplifyPat [p1, p2])
simplifyPat (ParenPattern          p) = simplifyPat p
simplifyPat (TuplePattern       _ ps)
  = ConstructorPattern (qTupleId (length ps)) (map simplifyPat ps)
simplifyPat (ListPattern        _ ps) =
  foldr (\e1 e2 -> ConstructorPattern qConsId [e1, e2])
        (ConstructorPattern qNilId []) (map simplifyPat ps)
simplifyPat (AsPattern           _ p) = simplifyPat p
simplifyPat (LazyPattern         _ _) = VariablePattern anonId
simplifyPat p                         = p

tidyPat :: Pattern -> Pattern
tidyPat p@(ConstructorPattern c ps)
  | isQTupleId c                   = TuplePattern noRef (map tidyPat ps)
  | c == qConsId && isFiniteList p = ListPattern [] (unwrapFinite p)
  | c == qConsId                   = unwrapInfinite p
  where
  isFiniteList (ConstructorPattern d [])                = d == qNilId
  isFiniteList (ConstructorPattern d es) | d == qConsId = isFiniteList (last es)
  isFiniteList _                                        = False

  unwrapInfinite (ConstructorPattern d [p1,p2])
    = InfixPattern (tidyPat p1) d (unwrapInfinite p2)
  unwrapInfinite p0                             = p0

  unwrapFinite (ConstructorPattern _ []     ) = []
  unwrapFinite (ConstructorPattern _ [p1,p2]) = tidyPat p1 : unwrapFinite p2
  unwrapFinite _                              = internalError $
    "WarnCheck.tidyPat.unwrapFinite"
tidyPat p = p

type ExhaustivePats = ([Pattern], [(Ident, [Literal])])

missingPattern :: [[Pattern]] -> WCM [ExhaustivePats]
missingPattern []          = return []
missingPattern eqs@(e:_)
  | null e                 = return []
  | any isLitPat firstPats = processLiterals eqs
  | any isConPat firstPats = processCons     eqs
  | all isVarPat firstPats = processVars     eqs
  | otherwise              = return []
  where firstPats = map firstPat eqs

processLiterals :: [[Pattern]] -> WCM [ExhaustivePats]
processLiterals []       = return []
processLiterals qs@(q:_) = do
  missing1 <- processUsedLiterals used_lits qs
  if null defaults
    then return $ defaultPat : missing1
    else do
      missing2 <- missingPattern defaults
      return $ [ (wildPat : ps, cs) | (ps, cs) <- missing2 ] ++ missing1
  where
  used_lits  = nub $ concatMap (getLit . firstPat) qs
  defaults   = [ shiftPat q' | q' <- qs, isVarPat (head q') ]
  defaultPat = ( VariablePattern new_var : replicate (length q - 1) wildPat
               , [(new_var, used_lits)])
  new_var    = mkIdent "x"

processUsedLiterals :: [Literal] -> [[Pattern]] -> WCM [ExhaustivePats]
processUsedLiterals lits qs = concat `liftM` mapM process lits
  where
  process lit = do
    missing <- missingPattern [shiftPat q | q <- qs, isVarLit lit (firstPat q)]
    return $ map (\(xs, ys) -> (LiteralPattern lit : xs, ys)) missing

processCons :: [[Pattern]] -> WCM [ExhaustivePats]
processCons []       = return []
processCons qs@(q:_) = do
  missing1 <- processUsedCons used_cons qs
  unused   <- getUnusedCons (map fst used_cons)
  if null unused
    then return missing1
    else if null defaults
      then return $ map defaultPat unused ++ missing1
      else do
        missing2 <- missingPattern defaults
        return $ [ (mkPattern c : ps, cs) | c <- unused, (ps, cs) <- missing2 ]
                  ++ missing1
  where
  used_cons    = nub $ concatMap (getCon . head) qs
  defaults     = [ shiftPat q' | q' <- qs, isVarPat (firstPat q') ]
  defaultPat c = (mkPattern c : replicate (length q - 1) wildPat, [])
  mkPattern (DataConstr c _ tys)
    = ConstructorPattern (qualifyLike (fst $ head used_cons) c)
                         (replicate (length tys) wildPat)

processUsedCons :: [(QualIdent, Int)] -> [[Pattern]] -> WCM [ExhaustivePats]
processUsedCons used qs = concat `liftM` mapM process used
  where
  process (c, a) = do
    let qs' = [ removeFirstCon c a q | q <- qs , isVarCon c (head q)]
    missing <- missingPattern qs'
    return $ map (\(xs, ys) -> (makeCon c a xs, ys)) missing

  makeCon c a ps = let (args, rest) = splitAt a ps
                   in ConstructorPattern c args : rest

  removeFirstCon c a (p:ps)
    | isVarPat p = replicate a wildPat ++ ps
    | isCon c  p = patArgs p           ++ ps
  removeFirstCon _ _ _ = internalError "Checks.WarnCheck.removeFirstCon"

processVars :: [[Pattern]] -> WCM [ExhaustivePats]
processVars eqs = do
  missing <- missingPattern (map shiftPat eqs)
  return $ map (\(xs, ys) -> (wildPat : xs, ys)) missing

getUnusedCons :: [QualIdent] -> WCM [DataConstr]
getUnusedCons []       = internalError "Checks.WarnCheck.getUnusedCons"
getUnusedCons qs@(q:_) = do
  allCons <- getConTy q >>= getTyCons . arrowBase
  return [ c | c@(DataConstr q' _ _) <- allCons, q' `notElem` map unqualify qs]

getConTy :: QualIdent -> WCM Type
getConTy q = do
  tyEnv <- gets valueEnv
  return $ case qualLookupValue q tyEnv of
    [DataConstructor  _ _ (ForAllExist _ _ ty)] -> ty
    [NewtypeConstructor _ (ForAllExist _ _ ty)] -> ty
    _                                           -> internalError $
      "Checks.WarnCheck.getConTy: " ++ show q

getTyCons :: Type -> WCM [DataConstr]
getTyCons (TypeConstructor tc _) = do
  tcEnv <- gets tyConsEnv
  return $ case lookupTC (unqualify tc) tcEnv of
    [DataType     _ _ cs] -> catMaybes cs
    [RenamingType _ _ nc] -> [nc]
    _ -> case qualLookupTC tc tcEnv of
      [DataType     _ _ cs] -> catMaybes cs
      [RenamingType _ _ nc] -> [nc]
      err                   -> internalError $
        "Checks.WarnCheck.getTyCons: " ++ show tc ++ ' ' : show err ++ '\n' : show tcEnv
getTyCons _ = internalError "Checks.WarnCheck.getTyCons"

firstPat :: [Pattern] -> Pattern
firstPat []    = internalError "Checks.WarnCheck.firstPat: empty list"
firstPat (p:_) = p

shiftPat :: [Pattern] -> [Pattern]
shiftPat []     = internalError "Checks.WarnCheck.shiftPat: empty list"
shiftPat (_:ps) = ps

wildPat :: Pattern
wildPat = VariablePattern anonId

getLit :: Pattern -> [Literal]
getLit (LiteralPattern l) = [l]
getLit _                  = []

getCon :: Pattern -> [(QualIdent, Int)]
getCon (ConstructorPattern c ps) = [(c, length ps)]
getCon _                         = []

isVarLit :: Literal -> Pattern -> Bool
isVarLit l p = isVarPat p || isLit l p

isVarCon :: QualIdent -> Pattern -> Bool
isVarCon c p = isVarPat p || isCon c p

isCon :: QualIdent -> Pattern -> Bool
isCon c (ConstructorPattern d _) = c == d
isCon _ _                        = False

isLit :: Literal -> Pattern -> Bool
isLit l (LiteralPattern m) = l == m
isLit _ _                  = False

isLitPat :: Pattern -> Bool
isLitPat (LiteralPattern  _) = True
isLitPat _                   = False

isVarPat :: Pattern -> Bool
isVarPat (VariablePattern _) = True
isVarPat _                   = False

isConPat :: Pattern -> Bool
isConPat (ConstructorPattern _ _) = True
isConPat      _                   = False

patArgs :: Pattern -> [Pattern]
patArgs (ConstructorPattern _ ps) = ps
patArgs _                         = []

-- -----------------------------------------------------------------------------

checkShadowing :: Ident -> WCM ()
checkShadowing x = warnFor WarnNameShadowing $
  shadowsVar x >>= maybe ok (report . warnShadowing x)

reportUnusedVars :: WCM ()
reportUnusedVars = warnFor WarnUnusedBindings $ do
  unused <- returnUnrefVars
  unless (null unused) $ mapM_ report $ map warnUnrefVar unused

reportUnusedTypeVars :: [Ident] -> WCM ()
reportUnusedTypeVars vs = warnFor WarnUnusedBindings $ do
  unused <- filterM isUnrefTypeVar vs
  unless (null unused) $ mapM_ report $ map warnUnrefTypeVar unused

-- ---------------------------------------------------------------------------
-- For detecting unreferenced variables, the following functions update the
-- current check state by adding identifiers occuring in declaration left hand
-- sides.

insertDecl :: Decl -> WCM ()
insertDecl (DataDecl     _ d _ cs) = do
  insertTypeConsId d
  mapM_ insertConstrDecl cs
insertDecl (TypeDecl     _ t _ ty) = do
  insertTypeConsId t
  insertTypeExpr ty
insertDecl (FunctionDecl    _ f _) = do
  cons <- isConsId f
  unless cons $ insertVar f
insertDecl (ForeignDecl _ _ _ f _) = insertVar f
insertDecl (ExternalDecl     _ vs) = mapM_ insertVar vs
insertDecl (PatternDecl     _ p _) = insertPattern False p
insertDecl (FreeDecl         _ vs) = mapM_ insertVar vs
insertDecl _                       = ok

insertTypeExpr :: TypeExpr -> WCM ()
insertTypeExpr (VariableType        _) = ok
insertTypeExpr (ConstructorType _ tys) = mapM_ insertTypeExpr tys
insertTypeExpr (TupleType         tys) = mapM_ insertTypeExpr tys
insertTypeExpr (ListType           ty) = insertTypeExpr ty
insertTypeExpr (ArrowType     ty1 ty2) = mapM_ insertTypeExpr [ty1,ty2]
insertTypeExpr (RecordType      _ rty) = do
  --mapM_ insertVar (concatMap fst fs)
  maybe (return ()) insertTypeExpr rty

insertConstrDecl :: ConstrDecl -> WCM ()
insertConstrDecl (ConstrDecl _ _    c _) = insertConsId c
insertConstrDecl (ConOpDecl  _ _ _ op _) = insertConsId op

-- 'fp' indicates whether 'checkPattern' deals with the arguments
-- of a function pattern or not.
-- Since function patterns are not recognized before syntax check, it is
-- necessary to determine whether a constructor pattern represents a
-- constructor or a function.
insertPattern :: Bool -> Pattern -> WCM ()
insertPattern fp (VariablePattern        v) = do
  cons <- isConsId v
  unless cons $ do
    var <- isVarId v
    if and [fp, var, not (isAnonId v)] then visitId v else insertVar v
insertPattern fp (ConstructorPattern  c ps) = do
  cons <- isQualConsId c
  mapM_ (insertPattern (not cons || fp)) ps
insertPattern fp (InfixPattern p1 c p2)
  = insertPattern fp (ConstructorPattern c [p1, p2])
insertPattern fp (ParenPattern           p) = insertPattern fp p
insertPattern fp (TuplePattern        _ ps) = mapM_ (insertPattern fp) ps
insertPattern fp (ListPattern         _ ps) = mapM_ (insertPattern fp) ps
insertPattern fp (AsPattern            v p) = insertVar v >> insertPattern fp p
insertPattern fp (LazyPattern          _ p) = insertPattern fp p
insertPattern _  (FunctionPattern     _ ps) = mapM_ (insertPattern True) ps
insertPattern _  (InfixFuncPattern p1 f p2)
  = insertPattern True (FunctionPattern f [p1, p2])
insertPattern fp (RecordPattern      fs r) = do
  mapM_ (insertFieldPattern fp) fs
  maybe (return ()) (insertPattern fp) r
insertPattern _ _ = ok

insertFieldPattern :: Bool -> Field Pattern -> WCM ()
insertFieldPattern fp (Field _ _ p) = insertPattern fp p

-- ---------------------------------------------------------------------------

-- Data type for distinguishing identifiers as either (type) constructors or
-- (type) variables (including functions).
data IdInfo
  = ConsInfo           -- ^ Constructor
  | VarInfo Ident Bool -- ^ Variable with original definition (for position)
                       --   and used flag
  deriving Show

isVariable :: IdInfo -> Bool
isVariable (VarInfo _ _) = True
isVariable _             = False

getVariable :: IdInfo -> Maybe Ident
getVariable (VarInfo v _) = Just v
getVariable _             = Nothing

isConstructor :: IdInfo -> Bool
isConstructor ConsInfo = True
isConstructor _        = False

variableVisited :: IdInfo -> Bool
variableVisited (VarInfo _ v) = v
variableVisited _             = True

visitVariable :: IdInfo -> IdInfo
visitVariable (VarInfo v _) = VarInfo v True
visitVariable  info         = info

insertScope :: QualIdent -> IdInfo -> WCM ()
insertScope qid info = modifyScope $ SE.insert qid info

insertVar :: Ident -> WCM ()
insertVar v = unless (isAnonId v) $ do
  known <- isKnownVar v
  if known then visitId v else insertScope (commonId v) (VarInfo v False)

insertTypeVar :: Ident -> WCM ()
insertTypeVar v = unless (isAnonId v)
                $ insertScope (typeId v) (VarInfo v False)

insertConsId :: Ident -> WCM ()
insertConsId c = insertScope (commonId c) ConsInfo

insertTypeConsId :: Ident -> WCM ()
insertTypeConsId c = insertScope (typeId c) ConsInfo

isVarId :: Ident -> WCM Bool
isVarId v = gets (isVar $ commonId v)

isConsId :: Ident -> WCM Bool
isConsId c = gets (isCons $ qualify c)

isQualConsId :: QualIdent -> WCM Bool
isQualConsId qid = gets (isCons qid)

shadowsVar :: Ident -> WCM (Maybe Ident)
shadowsVar v = gets (shadows $ commonId v)
  where
  shadows :: QualIdent -> WcState -> Maybe Ident
  shadows qid s = do
    (info, l) <- SE.lookupWithLevel qid sc
    guard (l < SE.currentLevel sc)
    getVariable info
    where sc = scope s

visitId :: Ident -> WCM ()
visitId v = modifyScope (SE.modify visitVariable (commonId v))

visitQId :: QualIdent -> WCM ()
visitQId v = do
  mid <- getModuleIdent
  maybe ok visitId (localIdent mid v)

visitTypeId :: Ident -> WCM ()
visitTypeId v = modifyScope (SE.modify visitVariable (typeId v))

visitQTypeId :: QualIdent -> WCM ()
visitQTypeId v = do
  mid <- getModuleIdent
  maybe ok visitTypeId (localIdent mid v)

isKnownVar :: Ident -> WCM Bool
isKnownVar v = gets $ \s -> isKnown s (commonId v)

isUnrefTypeVar :: Ident -> WCM Bool
isUnrefTypeVar v = gets (\s -> isUnref s (typeId v))

returnUnrefVars :: WCM [Ident]
returnUnrefVars = gets (\s ->
  let ids = map fst (SE.toLevelList (scope s))
      unrefs = filter (isUnref s) ids
  in  map unqualify unrefs )

inNestedScope :: WCM a -> WCM ()
inNestedScope m = beginScope >> m >> endScope

beginScope :: WCM ()
beginScope = modifyScope SE.beginScope

endScope :: WCM ()
endScope = modifyScope SE.endScopeUp

------------------------------------------------------------------------------

isKnown :: WcState -> QualIdent -> Bool
isKnown s qid = let sc = scope s
                in  isJust (SE.lookup qid sc)
                    && SE.level qid sc == SE.currentLevel sc

isUnref :: WcState -> QualIdent -> Bool
isUnref s qid = let sc = scope s
                in  maybe False (not . variableVisited) (SE.lookup qid sc)
                    && SE.level qid sc == SE.currentLevel sc

isVar :: QualIdent -> WcState -> Bool
isVar qid s = maybe (isAnonId (unqualify qid))
                    isVariable
                    (SE.lookup qid (scope s))

isCons :: QualIdent -> WcState -> Bool
isCons qid s = maybe (isImportedCons s qid)
                      isConstructor
                      (SE.lookup qid (scope s))
 where isImportedCons s' qid' = case qualLookupValue qid' (valueEnv s') of
          (DataConstructor  _ _ _) : _ -> True
          (NewtypeConstructor _ _) : _ -> True
          _                            -> False

-- Since type identifiers and normal identifiers (e.g. functions, variables
-- or constructors) don't share the same namespace, it is necessary
-- to distinguish them in the scope environment of the check state.
-- For this reason type identifiers are annotated with 1 and normal
-- identifiers are annotated with 0.
commonId :: Ident -> QualIdent
commonId = qualify . unRenameIdent

typeId :: Ident -> QualIdent
typeId = qualify . flip renameIdent 1

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

warnUnrefTypeVar :: Ident -> Message
warnUnrefTypeVar v = posMessage v $ hsep $ map text
  [ "Unreferenced type variable", escName v ]

warnUnrefVar :: Ident -> Message
warnUnrefVar v = posMessage v $ hsep $ map text
  [ "Unused declaration of variable", escName v ]

warnShadowing :: Ident -> Ident -> Message
warnShadowing x v = posMessage x $
  text "Shadowing symbol" <+> text (escName x)
  <> comma <+> text "bound at:" <+> ppPosition (getPosition v)

warnIdleCaseAlts :: Position -> Message
warnIdleCaseAlts p = posMessage p $ text "Idle case alternative(s)"

warnOverlappingCaseAlts :: [Alt] -> Message
warnOverlappingCaseAlts [] = internalError
  "WarnCheck.warnOverlappingCaseAlts: empty list"
warnOverlappingCaseAlts alts@(Alt p _ _ : _) = posMessage p $ text
  "Overlapping case alternatives" $+$ nest 2 (vcat (map myppAlt alts))
  where myppAlt (Alt pos pat _) = ppLine pos <> text ":" <+> ppPattern 0 pat

warnMissingPattern :: String -> Position -> [ExhaustivePats] -> Message
warnMissingPattern loc p pats = posMessage p
  $   text "Pattern matches are non-exhaustive"
  $+$ text "In a" <+> text loc <> char ':'
  $+$ nest 2 (text "Patterns not matched:" $+$ nest 2 (vcat (ppExPats pats)))
  where
  ppExPats ps
    | length ps > maxMissingPattern = ppPats ++ [text "..."]
    | otherwise                     = ppPats
    where ppPats = map ppExPat (take maxMissingPattern ps)
  ppExPat (ps, cs)
    | null cs   = ppPats
    | otherwise = ppPats <+> text "with" <+> hsep (map ppCons cs)
    where ppPats = hsep (map (ppPattern 2) ps)
  ppCons (i, lits) = ppIdent i <+> text "`notElem`"
                 <+> ppExpr 0 (List [] (map Literal lits))

maxMissingPattern :: Int
maxMissingPattern = 4
