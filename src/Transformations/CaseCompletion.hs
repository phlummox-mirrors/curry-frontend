{- |CaseCompletion - expands case branches with missing constructors

    The MMC translates case expressions into the intermediate language
    representation (IL) without completing them (i.e. without generating
    case branches for missing contructors). Because they are necessary for
    the PAKCS back end, this module expands all case expressions accordingly.

    May 2005, Martin Engelke, (men@informatik.uni-kiel.de)
-}
module Transformations.CaseCompletion (completeCase) where

import Control.Monad (liftM, liftM2)
import qualified Control.Monad.State as S
import Data.List (find, nubBy)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)

import Curry.Base.Ident
import Curry.Base.Position (SrcRef)
import qualified Curry.Syntax as CS

import Base.Messages (internalError)
import Env.Interface (InterfaceEnv, lookupInterface)
import IL

-- Completes case expressions by adding branches for missing constructors.
-- The interface environment 'menv' is needed to compute these constructors.
completeCase :: InterfaceEnv -> Module -> Module
completeCase iEnv mdl@(Module mid is ds) = Module mid is ds'
 where ds'= S.evalState (mapM (withLocalEnv . ccDecl) ds)
                        (CCState mdl iEnv (getModuleScope mdl))

data CCState = CCState
  { modul        :: Module
  , interfaceEnv :: InterfaceEnv
  , scopeEnv     :: ScopeEnv
  }

type CCM a = S.State CCState a

getModule :: CCM Module
getModule = S.gets modul

getInterfaceEnv :: CCM InterfaceEnv
getInterfaceEnv = S.gets interfaceEnv

modifyScopeEnv :: (ScopeEnv -> ScopeEnv) -> CCM ()
modifyScopeEnv f = S.modify $ \ s -> s { scopeEnv = f $ scopeEnv s }

getScopeEnv :: CCM ScopeEnv
getScopeEnv = S.gets scopeEnv

withLocalEnv :: CCM a -> CCM a
withLocalEnv act = do
  oldEnv <- getScopeEnv
  res <- act
  modifyScopeEnv $ const oldEnv
  return res

inNestedScope :: CCM a -> CCM a
inNestedScope act = modifyScopeEnv beginScope >> act

-- The following functions traverse an IL term searching for case expressions

ccDecl :: Decl -> CCM Decl
ccDecl dd@(DataDecl        _ _ _) = return dd
ccDecl nt@(NewtypeDecl     _ _ _) = return nt
ccDecl (FunctionDecl qid vs ty e) = inNestedScope $ do
  modifyScopeEnv (flip (foldr insertIdent) vs)
  FunctionDecl qid vs ty `liftM` ccExpr e
ccDecl ed@(ExternalDecl  _ _ _ _) = return ed

ccExpr :: Expression -> CCM Expression
ccExpr l@(Literal       _) = return l
ccExpr v@(Variable      _) = return v
ccExpr f@(Function    _ _) = return f
ccExpr c@(Constructor _ _) = return c
ccExpr (Apply       e1 e2) = liftM2 Apply (ccExpr e1) (ccExpr e2)
ccExpr (Case  r ea e alts) = do
  e'    <- ccExpr e
  senv1 <- getScopeEnv
  altsR <- removeRedundantAlts `liftM` mapM ccAlt alts
  case () of
    _ | null altsR       -> internalError "CaseCompletion.ccExpr: empty alternative list"
      -- pattern matching causes flexible case expressions
      | ea == Flex       -> modifyScopeEnv (const senv1) >> return (Case r ea e' altsR)
      | isConstrAlt altR ->          completeConsAlts r ea e' altsR
      | isLitAlt    altR -> return $ completeLitAlts  r ea e' altsR
      | isVarAlt    altR -> return $ completeVarAlts       e' altsR
      | otherwise        -> internalError "CaseCompletion.ccExpr: illegal alternative list"
      where altR  = head altsR

ccExpr (Or    e1 e2) = liftM2 Or (ccExpr e1) (ccExpr e2)
ccExpr (Exist   v e) = inNestedScope $ do
  modifyScopeEnv $ insertIdent v
  Exist v `liftM` ccExpr e
ccExpr (Let     b e) = inNestedScope $ do
  modifyScopeEnv $ insertBinding b
  liftM2 (flip Let) (ccExpr e) (ccBinding b)
ccExpr (Letrec bs e) = inNestedScope $ do
  modifyScopeEnv $ flip (foldr insertBinding) bs
  liftM2 (flip Letrec) (ccExpr e) (mapM ccBinding bs)

ccAlt :: Alt -> CCM Alt
ccAlt (Alt p e) = inNestedScope $ do
  modifyScopeEnv $ insertConstrTerm p
  Alt p `liftM` ccExpr e

ccBinding :: Binding -> CCM Binding
ccBinding (Binding v e) = Binding v `liftM` ccExpr e

-- ---------------------------------------------------------------------------
-- The function 'removeRedundantAlts' removes case branches which are
-- either unreachable or multiply declared.
-- Note: unlike the PAKCS frontend, MCC does not support warnings. So
-- there will be no messages if alternatives have been removed.

removeRedundantAlts :: [Alt] -> [Alt]
removeRedundantAlts = removeMultipleAlts . removeIdleAlts

-- An alternative is idle if it occurs anywhere behind another alternative
-- which contains a variable pattern. Example:
--    case x of
--      (y:ys) -> e1
--      z      -> e2
--      []     -> e3
-- Here all alternatives behind (z  -> e2) are idle and will be removed.
removeIdleAlts ::[Alt] -> [Alt]
removeIdleAlts = fst . splitAfter isVarAlt
  where
  -- Splits a list behind the first element which satifies 'p'
  splitAfter :: (a -> Bool) -> [a] -> ([a], [a])
  splitAfter p xs = go [] xs
    where
    go fs []                 = (reverse fs    , [])
    go fs (y:ys) | p y       = (reverse (y:fs), ys)
                | otherwise = go (y:fs) ys

-- An alternative occurs multiply if at least two alternatives
-- use the same pattern. Example:
--    case x of
--      []     -> e1
--      (y:ys) -> e2
--      []     -> e3
-- Here, the last alternative occures multiply because its pattern is already
-- used in the first alternative. All multiple alternatives will be
-- removed except for the first occurrence.
removeMultipleAlts :: [Alt] -> [Alt]
removeMultipleAlts = nubBy eqAlt
  where eqAlt (Alt p1 _) (Alt p2 _) = case (p1, p2) of
          (LiteralPattern       l1, LiteralPattern       l2) -> l1 == l2
          (ConstructorPattern c1 _, ConstructorPattern c2 _) -> c1 == c2
          (VariablePattern       _, VariablePattern       _) -> True
          _                                                  -> False

-- ---------------------------------------------------------------------------
-- Functions for completing case alternatives

-- Completes a case alternative list which branches via constructor patterns
-- by adding alternatives of the form
--
--      comp_pattern -> default_expr
--
-- where "comp_pattern" is a complementary constructor pattern and
-- "default_expr" is the expression from the first alternative containing
-- a variable pattern. If there is no such alternative, the default expression
-- is set to the prelude function 'failed'.
--
-- This funtions uses a scope environment ('ScopeEnv') to generate fresh
-- variables for the arguments of the new constructors.
completeConsAlts :: SrcRef -> Eval -> Expression -> [Alt] -> CCM Expression
completeConsAlts r ea expr alts = do
  mdl       <- getModule
  menv      <- getInterfaceEnv
  -- complementary constructors
  complCons <- mapM genConstrTerm $ getComplConstrs mdl menv
               [ c | (Alt (ConstructorPattern c _) _) <- consAlts ]
  -- complementary alternatives
  let complAlts = map (\c -> Alt c $ replaceVar v (pattern2Expr c) de)
                  complCons
  return $ Case r ea expr (consAlts ++ complAlts)
  where
  -- existing contructor pattern alternatives
  consAlts = filter isConstrAlt alts

  -- default alternative
  -- Note: the newly generated variable 'x!' is just a dummy and will never
  -- occur in the transformed program
  (Alt (VariablePattern v) de)
    = fromMaybe (Alt (VariablePattern (mkIdent "x!")) failedExpr)
    $ find isVarAlt alts

  genConstrTerm (qid, arity) = do
    senv <- getScopeEnv
    let args  = genIdentList arity "x" senv
    modifyScopeEnv $ flip (foldr insertIdent) args
    return $ ConstructorPattern qid args

-- If the alternatives branches via literal pattern complementary
-- constructor list cannot be generated because it would become infinite.
-- So the function 'completeLitAlts' transforms case expressions like
--      case <ce> of
--        <lit_1> -> <expr_1>
--        <lit_2> -> <expr_2>
--                    :
--        <lit_n> -> <expr_n>
--       [<var>   -> <default_expr>]
-- to
--      case (<ce> == <lit_1>) of
--        True  -> <expr_1>
--        False -> case (<ce> == <lit_2>) of
--                   True  -> <expr_2>
--                   False -> case ...
--                                  :
--                               -> case (<ce> == <lit_n>) of
--                                    True  -> <expr_n>
--                                    False -> <default_expr>
--
completeLitAlts :: SrcRef -> Eval -> Expression -> [Alt] -> Expression
completeLitAlts _ _  _  []                = failedExpr
completeLitAlts r ea ce (Alt p ae : alts) = case p of
  LiteralPattern l  -> Case r ea (ce `eqExpr` Literal l)
                       [ Alt truePatt  ae
                       , Alt falsePatt (completeLitAlts r ea ce alts)
                       ]
  VariablePattern v -> replaceVar v ce ae
  _ -> internalError "CaseCompletion.completeLitAlts: illegal alternative"

-- For the unusual case of only one alternative containing a variable pattern,
-- it is necessary to tranform it to a 'let' term because FlatCurry does not
-- support variable patterns in case alternatives. So the case expression
--    case <ce> of
--      x -> <ae>
-- is transformed to
--      let x = <ce> in <ae>
completeVarAlts :: Expression -> [Alt] -> Expression
completeVarAlts _  []             = failedExpr
completeVarAlts ce (Alt p ae : _) = case p of
  VariablePattern x -> Let (Binding x ce) ae
  _                 -> internalError $
    "CaseCompletion.completeVarAlts: variable pattern expected"

-- ---------------------------------------------------------------------------
-- Some functions for testing case alternatives

isVarAlt :: Alt -> Bool
isVarAlt (Alt (VariablePattern _) _) = True
isVarAlt _                           = False

isConstrAlt :: Alt -> Bool
isConstrAlt (Alt (ConstructorPattern _ _) _) = True
isConstrAlt _                                = False

isLitAlt :: Alt -> Bool
isLitAlt (Alt (LiteralPattern _) _) = True
isLitAlt _                          = False

-- ---------------------------------------------------------------------------
-- This part of the module contains functions for replacing variables
-- with expressions. This is necessary in the case of having a default
-- alternative like
--      v -> <expr>
-- where the variable v occurs in the default expression <expr>. When
-- building additional alternatives for this default expression, the variable
-- must be replaced with the newly generated constructors.
replaceVar :: Ident -> Expression -> Expression -> Expression
replaceVar v e x@(Variable    w)
  | v == w    = e
  | otherwise = x
replaceVar v e (Apply     e1 e2)
  = Apply (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Case r ev e' bs)
  = Case r ev (replaceVar v e e') (map (replaceVarInAlt v e) bs)
replaceVar v e (Or        e1 e2)
  = Or (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Exist      w e')
   | v == w                        = Exist w e'
   | otherwise                     = Exist w (replaceVar v e e')
replaceVar v e (Let        b e')
   | v `occursInBinding` b         = Let b e'
   | otherwise                     = Let (replaceVarInBinding v e b)
                                         (replaceVar v e e')
replaceVar v e (Letrec    bs e')
   | any (occursInBinding v) bs = Letrec bs e'
   | otherwise                     = Letrec (map (replaceVarInBinding v e) bs)
                                            (replaceVar v e e')
replaceVar _ _ e'               = e'

replaceVarInAlt :: Ident -> Expression -> Alt -> Alt
replaceVarInAlt v e (Alt p e')
  | v `occursInPattern` p = Alt p e'
  | otherwise             = Alt p (replaceVar v e e')

replaceVarInBinding :: Ident -> Expression -> Binding -> Binding
replaceVarInBinding v e (Binding w e')
  | v == w    = Binding w e'
  | otherwise = Binding w (replaceVar v e e')

occursInPattern :: Ident -> ConstrTerm -> Bool
occursInPattern v (VariablePattern       w) = v == w
occursInPattern v (ConstructorPattern _ vs) = v `elem` vs
occursInPattern _ _                         = False

occursInBinding :: Ident -> Binding -> Bool
occursInBinding v (Binding w _) = v == w

-- ---------------------------------------------------------------------------
-- The following functions generate several IL expressions and patterns

failedExpr :: Expression
failedExpr = Function (qualifyWith preludeMIdent (mkIdent "failed")) 0

eqExpr :: Expression -> Expression -> Expression
eqExpr e1 e2 = Apply (Apply eq e1) e2
  where eq = Function (qualifyWith preludeMIdent (mkIdent "==")) 2

truePatt :: ConstrTerm
truePatt = ConstructorPattern qTrueId []

falsePatt :: ConstrTerm
falsePatt = ConstructorPattern qFalseId []

pattern2Expr :: ConstrTerm -> Expression
pattern2Expr (LiteralPattern        l) = Literal l
pattern2Expr (VariablePattern       v) = Variable v
pattern2Expr (ConstructorPattern c ts) = foldl Apply
  (Constructor c (length ts)) (map Variable ts)

-- ---------------------------------------------------------------------------
-- The following functions compute the missing constructors for generating
-- missing case alternatives

-- Computes the complementary constructors for a given list of constructors.
-- All specified constructors must be of the same type.
-- This functions uses the module environment 'menv', which contains all
-- imported constructors, except for the built-in list constructors.
-- TODO: Check if the list constructors are in the menv.
getComplConstrs :: Module -> InterfaceEnv -> [QualIdent] -> [(QualIdent, Int)]
getComplConstrs _                 _    []
  = internalError "CaseCompletion.getComplConstrs: empty constructor list"
getComplConstrs (Module mid _ ds) menv cs@(c:_)
  -- built-in lists
  | c `elem` [qNilId, qConsId] = complementary cs [(qNilId, 0), (qConsId, 2)]
  -- current module
  | mid' == mid                = getCCFromDecls cs ds
  -- imported module
  | otherwise                  = maybe [] (getCCFromIDecls mid' cs)
                                          (lookupInterface mid' menv)
  where mid' = fromMaybe mid (qidModule c)

-- Find complementary constructors within the declarations of the
-- current module
getCCFromDecls :: [QualIdent] -> [Decl] -> [(QualIdent, Int)]
getCCFromDecls cs ds = complementary cs cinfos
  where
  cinfos = map constrInfo
         $ maybe [] extractConstrDecls (find (`declares` head cs) ds)

  decl `declares` qid = case decl of
    DataDecl    _ _ cs' -> any (`declaresConstr` qid) cs'
    NewtypeDecl _ _ nc  -> nc `declaresConstr` qid
    _                   -> False

  declaresConstr (ConstrDecl cid _) qid = cid == qid

  extractConstrDecls (DataDecl _ _ cs') = cs'
  extractConstrDecls _                  = []

  constrInfo (ConstrDecl cid tys) = (cid, length tys)

-- Find complementary constructors within the module environment
getCCFromIDecls :: ModuleIdent -> [QualIdent] -> CS.Interface -> [(QualIdent, Int)]
getCCFromIDecls mid cs (CS.Interface _ _ ds) = complementary cs cinfos
  where
  cinfos = map constrInfo
         $ maybe [] extractConstrDecls (find (`declares` head cs) ds)

  decl `declares` qid = case decl of
    CS.IDataDecl    _ _ _ cs' -> any (`declaresConstr` qid) $ catMaybes cs'
    CS.INewtypeDecl _ _ _ nc  -> p_isINewConstrDecl qid nc
    _                         -> False

  declaresConstr (CS.ConstrDecl  _ _ cid _) qid = unqualify qid == cid
  declaresConstr (CS.ConOpDecl _ _ _ oid _) qid = unqualify qid == oid

  p_isINewConstrDecl qid (CS.NewConstrDecl _ _ cid _) = unqualify qid == cid

  extractConstrDecls (CS.IDataDecl _ _ _ cs') = catMaybes cs'
  extractConstrDecls _                        = []

  constrInfo (CS.ConstrDecl _ _ cid tys) = (qualifyWith mid cid, length tys)
  constrInfo (CS.ConOpDecl  _ _ _ oid _) = (qualifyWith mid oid, 2)

-- Compute complementary constructors
complementary :: [QualIdent] -> [(QualIdent, Int)] -> [(QualIdent, Int)]
complementary known others = filter ((`notElem` known) . fst) others

-- ---------------------------------------------------------------------------
-- ScopeEnv stuff
-- 2011-02-08 (bjp): Moved from IL.Scope
-- Moved from Base.OldScopeEnv on 2012-09-04
-- ---------------------------------------------------------------------------

getModuleScope :: Module -> ScopeEnv
getModuleScope (Module _ _ ds) = foldr insertDecl newScopeEnv ds

insertDecl :: Decl -> ScopeEnv -> ScopeEnv
insertDecl (DataDecl      qid _ cs) = flip (foldr insertConstrDecl) cs
                                    . insertQIdent qid
insertDecl (NewtypeDecl    qid _ c) = insertConstrDecl c
                                    . insertQIdent qid
insertDecl (FunctionDecl qid _ _ _) = insertQIdent qid
insertDecl (ExternalDecl qid _ _ _) = insertQIdent qid

insertConstrDecl :: ConstrDecl a -> ScopeEnv -> ScopeEnv
insertConstrDecl (ConstrDecl qid _) = insertQIdent qid

insertConstrTerm :: ConstrTerm -> ScopeEnv -> ScopeEnv
insertConstrTerm (LiteralPattern        _) = id
insertConstrTerm (ConstructorPattern _ vs) = flip (foldr insertIdent) vs
insertConstrTerm (VariablePattern       v) = insertIdent v

insertBinding :: Binding -> ScopeEnv -> ScopeEnv
insertBinding (Binding v _) = insertIdent v

-- Type for representing an environment containing identifiers in several
-- scope levels
type ScopeLevel = Integer
type ScopeEnv   = (IdEnv, [IdEnv], ScopeLevel)
-- (top-level IdEnv, stack of lower level IdEnv, current level)
-- Invariant: The current level is the number of stack elements

-- Generates a new instance of a scope table
newScopeEnv :: ScopeEnv
newScopeEnv = (Map.empty, [], 0)

-- Increase the level of the scope.
beginScope :: ScopeEnv -> ScopeEnv
beginScope (topLevel, []    , _    ) = (topLevel, [Map.empty], 1)
beginScope (topLevel, (l:ls), level) = (topLevel, (l:l:ls)   , level + 1)

-- Insert an identifier into the current level of the scope environment
insertIdent :: Ident -> ScopeEnv -> ScopeEnv
insertIdent ident (topLevel, nested, level) = case nested of
  []     -> (insertInto topLevel, []                 , 0    )
  lt:lts -> (topLevel           , insertInto lt : lts, level)
  where insertInto = insertId level ident

insertQIdent :: QualIdent -> ScopeEnv -> ScopeEnv
insertQIdent q = insertIdent (unqualify q)

-- Generates a list of new identifiers where each identifier has
-- the prefix 'name' followed by an index (i.e., "var3" if 'name' was "var").
-- All returned identifiers are unique within the current scope.
genIdentList :: Int -> String -> ScopeEnv -> [Ident]
genIdentList = p_genIdentList 0
  where
  p_genIdentList :: Int -> Int -> String -> ScopeEnv -> [Ident]
  p_genIdentList i s n env
    | s == 0    = []
    | otherwise = case genIdent (n ++ show i) env of
        Nothing    ->         p_genIdentList (i + 1) s       n  env
        Just ident -> ident : p_genIdentList (i + 1) (s - 1) n (insertIdent ident env)

  -- Generates a new identifier for the specified name. The new identifier is
  -- unique within the current scope. If no identifier can be generated for
  -- 'name', then 'Nothing' will be returned
  genIdent :: String -> ScopeEnv -> Maybe Ident
  genIdent name (topLevel, []      , _) = genId name topLevel
  genIdent name (_       , (lt : _), _) = genId name lt

-- The IdEnv is an environment which stores the level in which an identifier
-- was defined, starting with 0 for the top-level.
type IdEnv = Map.Map (Either String Integer) Integer

insertId :: Integer -> Ident -> IdEnv -> IdEnv
insertId lvl i = Map.insert (Left  (idName   i)) lvl
               . Map.insert (Right (idUnique i)) lvl

genId :: String -> IdEnv -> Maybe Ident
genId n env | Left n `Map.member` env  = Nothing
            | otherwise                = Just (try 0)
  where try i
            | Right i `Map.member` env = try (i + 1)
            | otherwise                = renameIdent (mkIdent n) i
