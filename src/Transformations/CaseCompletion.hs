{- |
    Module      :  $Header$
    Description :  CaseCompletion
    Copyright   :  (c) 2005       , Martin Engelke
                       2011 - 2015, Björn Peemöller
                       2015       , Jan Tikovsky
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  non-portable (DeriveDataTypeable)

    This module expands case branches with missing constructors.

    The MCC translates case expressions into the intermediate language
    representation (IL) without completing them (i.e. without generating
    case branches for missing contructors), because the intermediate language
    supports variable patterns for the fallback case.
    In contrast, the FlatCurry representation of patterns only allows
    literal and constructor patterns, which requires the expansion
    default branches to all missing constructors.

    This is only necessary for *rigid* case expressions, because any
    *flexible* case expression with more than one branch and a variable
    pattern is non-deterministic. In consequence, these overlapping patterns
    have already been eliminated in the pattern matching compilation
    process (see module CurryToIL).

    To summarize, this module expands all rigid case expressions.
-}
{-# LANGUAGE CPP #-}
module Transformations.CaseCompletion (completeCase) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import qualified Control.Monad.State as S   (State, evalState, gets, modify)
import           Data.List                  (find)
import           Data.Maybe                 (fromMaybe, listToMaybe)

import           Curry.Base.Ident
import           Curry.Base.Position        (SrcRef)
import qualified Curry.Syntax        as CS

import Base.Expr
import Base.Messages                        (internalError)
import qualified Base.ScopeEnv       as SE
  (ScopeEnv, new, beginScope, insert, exists)
import Env.Interface                        (InterfaceEnv, lookupInterface)
import IL

-- Completes case expressions by adding branches for missing constructors.
-- The interface environment 'iEnv' is needed to compute these constructors.
completeCase :: InterfaceEnv -> Module -> Module
completeCase iEnv mdl@(Module mid is ds) = Module mid is ds'
 where ds'= S.evalState (mapM (withLocalEnv . ccDecl) ds)
                        (CCState mdl iEnv (getModuleScope mdl))

-- -----------------------------------------------------------------------------
-- Internally used state monad
-- -----------------------------------------------------------------------------

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
inNestedScope act = modifyScopeEnv SE.beginScope >> act

-- -----------------------------------------------------------------------------
-- The following functions traverse an IL term searching for case expressions
-- -----------------------------------------------------------------------------

ccDecl :: Decl -> CCM Decl
ccDecl dd@(DataDecl        _ _ _) = return dd
ccDecl nt@(NewtypeDecl     _ _ _) = return nt
ccDecl (FunctionDecl qid vs ty e) = inNestedScope $ do
  modifyScopeEnv (flip (foldr insertIdent) vs)
  FunctionDecl qid vs ty <$> ccExpr e
ccDecl ed@(ExternalDecl  _ _ _ _) = return ed

ccExpr :: Expression -> CCM Expression
ccExpr l@(Literal       _) = return l
ccExpr v@(Variable      _) = return v
ccExpr f@(Function    _ _) = return f
ccExpr c@(Constructor _ _) = return c
ccExpr (Apply       e1 e2) = Apply <$> ccExpr e1 <*> ccExpr e2
ccExpr (Case    r ea e bs) = do
  e'  <- ccExpr e
  bs' <- mapM ccAlt bs
  ccCase r ea e' bs'
ccExpr (Or          e1 e2) = Or <$> ccExpr e1 <*> ccExpr e2
ccExpr (Exist         v e) = inNestedScope $ do
  modifyScopeEnv $ insertIdent v
  Exist v <$> ccExpr e
ccExpr (Let           b e) = inNestedScope $ do
  modifyScopeEnv $ insertBinding b
  flip Let <$> ccExpr e <*> ccBinding b
ccExpr (Letrec       bs e) = inNestedScope $ do
  modifyScopeEnv $ flip (foldr insertBinding) bs
  flip Letrec <$> ccExpr e <*> mapM ccBinding bs
ccExpr (Typed        e ty) = flip Typed ty <$> ccExpr e

ccAlt :: Alt -> CCM Alt
ccAlt (Alt p e) = inNestedScope $ do
  modifyScopeEnv $ insertConstrTerm p
  Alt p <$> ccExpr e

ccBinding :: Binding -> CCM Binding
ccBinding (Binding v e) = Binding v <$> ccExpr e

-- ---------------------------------------------------------------------------
-- Functions for completing case alternatives
-- ---------------------------------------------------------------------------
ccCase :: SrcRef -> Eval -> Expression -> [Alt] -> CCM Expression
-- flexible cases are not completed
ccCase r Flex  e alts     = return $ Case r Flex e alts
ccCase _ Rigid _ []       = internalError $ "CaseCompletion.ccCase: "
                                         ++ "empty alternative list"
ccCase r Rigid e as@(Alt p _:_) = case p of
  ConstructorPattern _ _ -> completeConsAlts r Rigid e as
  LiteralPattern     _   -> completeLitAlts  r Rigid e as
  VariablePattern    _   -> completeVarAlts          e as

-- Completes a case alternative list which branches via constructor patterns
-- by adding alternatives. Thus, case expressions of the form
--     case <ce> of
--       <C_1> -> <expr_1>
--              :
--       <C_n> -> <expr_n>
--      [<var> -> <default_expr>]
-- are in general extended to
--     let x = <ce> in
--     let y = <default_expr>[<var>/x] in
--     case x of
--       <C_1>  -> <expr_1>
--               :
--       <C_n>  -> <expr_n>
--       <C'_1> -> y
--               :
--       <C'_m> -> y
-- where the C'_j are the complementary constructor patterns of the C_i,
-- @x@ and @y@ are fresh variables, and "default_expr" is the expression
-- from the first alternative containing a variable pattern. If there is no such
-- alternative, the default expression is set to the prelude function 'failed'.
-- In addition, there are a few optimizations performed to avoid the
-- construction of unnecessary let-bindings:
--   - If there are no complementary patterns, the expression remains unchanged.
--   - If there is only one complementary pattern,
--     the binding for @y@ is avoided (see @bindDefVar@).
--   - If the variable @<var>@ does not occur in the default expression,
--     the binding for @x@ is avoided (see @mkCase@).
completeConsAlts :: SrcRef -> Eval -> Expression -> [Alt] -> CCM Expression
completeConsAlts r ea ce alts = do
  mdl       <- getModule
  menv      <- getInterfaceEnv
  -- complementary constructor patterns
  complPats <- mapM genPat $ getComplConstrs mdl menv
               [ c | (Alt (ConstructorPattern c _) _) <- consAlts ]
  [v, w] <- newIdentList 2 "x"
  return $ case (complPats, defaultAlt v) of
            (_:_, Just e') -> bindDefVar v ce w e' complPats
            _              -> Case r ea ce consAlts
  where
  -- existing contructor pattern alternatives
  consAlts = [ a | a@(Alt (ConstructorPattern _ _) _) <- alts ]

  -- generate a new constructor pattern
  genPat (qid, arity) = ConstructorPattern qid <$> newIdentList arity "x"

  -- default alternative, if there is one
  defaultAlt v = listToMaybe [ replaceVar x (Variable v) e
                             | Alt (VariablePattern x) e <- alts ]

  -- create a binding for @v = e@ if needed
  bindDefVar v e w e' ps
    | v `elem` fv e' = mkBinding v e $ mkCase (Variable v) w e' ps
    | otherwise      = mkCase e w e' ps

  -- create a binding for @w = e'@ if needed, and a case expression
  -- @case e of { consAlts ++ (ps -> w) }@
  mkCase e w e' ps = case ps of
    [p] -> Case r ea e (consAlts ++ [Alt p e'])
    _   -> mkBinding w e'
         $ Case r ea e (consAlts ++ [Alt p (Variable w) | p <- ps])

-- If the alternatives' branches contain literal patterns, a complementary
-- constructor list cannot be generated because it would become potentially
-- infinite. Thus, function 'completeLitAlts' transforms case expressions like
--     case <ce> of
--       <lit_1> -> <expr_1>
--       <lit_2> -> <expr_2>
--                   :
--       <lit_n> -> <expr_n>
--      [<var>   -> <default_expr>]
-- to
--     let x = <ce> in
--     case (v == <lit_1>) of
--       True  -> <expr_1>
--       False -> case (x == <lit_2>) of
--                  True  -> <expr_2>
--                  False -> case ...
--                                 :
--                               -> case (x == <lit_n>) of
--                                    True  -> <expr_n>
--                                    False -> <default_expr>
-- If the default expression is missing, @failed@ is used instead.
completeLitAlts :: SrcRef -> Eval -> Expression -> [Alt] -> CCM Expression
completeLitAlts r ea ce alts = do
  [x] <- newIdentList 1 "x"
  return $ mkBinding x ce $ nestedCases x alts
  where
  nestedCases _ []              = failedExpr
  nestedCases x (Alt p ae : as) = case p of
    LiteralPattern l  -> Case r ea (Variable x `eqExpr` Literal l)
                          [ Alt truePatt  ae
                          , Alt falsePatt (nestedCases x as)
                          ]
    VariablePattern v -> replaceVar v (Variable x) ae
    _ -> internalError "CaseCompletion.completeLitAlts: illegal alternative"

-- For the unusual case of only one alternative containing a variable pattern,
-- it is necessary to tranform it to a 'let' term because FlatCurry does not
-- support variable patterns in case alternatives. So the case expression
--    case <ce> of
--      x -> <ae>
-- is transformed to
--      let x = <ce> in <ae>
completeVarAlts :: Expression -> [Alt] -> CCM Expression
completeVarAlts _  []             = return failedExpr
completeVarAlts ce (Alt p ae : _) = case p of
  VariablePattern x -> return $ mkBinding x ce ae
  _                 -> internalError $
    "CaseCompletion.completeVarAlts: variable pattern expected"

-- Smart constructor for non-recursive let-binding. @mkBinding v e e'@
-- evaluates to @e'[v/e]@ if @e@ is a variable, or @let v = e in e'@ otherwise.
mkBinding :: Ident -> Expression -> Expression -> Expression
mkBinding v e e' = case e of
  Variable _ -> replaceVar v e e'
  _          -> Let (Binding v e) e'

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
   | v == w                     = Exist w e'
   | otherwise                  = Exist w (replaceVar v e e')
replaceVar v e (Let        b e')
   | v `occursInBinding` b      = Let b e'
   | otherwise                  = Let (replaceVarInBinding v e b)
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
    CS.IDataDecl    _ _ _ cs' _ -> any (`declaresConstr` qid) cs'
    CS.INewtypeDecl _ _ _ nc  _ -> isNewConstrDecl qid nc
    _                           -> False

  declaresConstr (CS.ConstrDecl  _ _ cid _) qid = unqualify qid == cid
  declaresConstr (CS.ConOpDecl _ _ _ oid _) qid = unqualify qid == oid
  declaresConstr (CS.RecordDecl  _ _ cid _) qid = unqualify qid == cid

  isNewConstrDecl qid (CS.NewConstrDecl _ _ cid _) = unqualify qid == cid
  isNewConstrDecl qid (CS.NewRecordDecl _ _ cid _) = unqualify qid == cid

  extractConstrDecls (CS.IDataDecl _ _ _ cs' _) = cs'
  extractConstrDecls _                          = []

  constrInfo (CS.ConstrDecl _ _ cid tys) = (qualifyWith mid cid, length tys)
  constrInfo (CS.ConOpDecl  _ _ _ oid _) = (qualifyWith mid oid, 2)
  constrInfo (CS.RecordDecl _ _ cid  fs) = (qualifyWith mid cid, length labels)
    where labels = [l | CS.FieldDecl _ ls _ <- fs, l <- ls]

-- Compute complementary constructors
complementary :: [QualIdent] -> [(QualIdent, Int)] -> [(QualIdent, Int)]
complementary known others = filter ((`notElem` known) . fst) others

-- ---------------------------------------------------------------------------
-- ScopeEnv stuff
-- ---------------------------------------------------------------------------

-- Type for representing an environment containing identifiers in several
-- scope levels
type ScopeEnv = SE.ScopeEnv (Either String Integer) ()

insertIdent :: Ident -> ScopeEnv -> ScopeEnv
insertIdent i = SE.insert (Left  (idName   i)) ()
              . SE.insert (Right (idUnique i)) ()

newIdentList :: Int -> String -> CCM [Ident]
newIdentList num str = genIdentList num (0 :: Integer)
  where
  -- Generates a list of new identifiers where each identifier has
  -- the prefix 'name' followed by an index (i.e., "var3" if 'name' was "var").
  -- All returned identifiers are unique within the current scope.
  genIdentList s i
    | s == 0    = return []
    | otherwise = do
      env <- getScopeEnv
      case genIdent (str ++ show i) env of
        Nothing    -> genIdentList s (i + 1)
        Just ident -> do
          modifyScopeEnv $ insertIdent ident
          idents <- genIdentList (s - 1) (i + 1)
          return (ident : idents)

  -- Generates a new identifier for the specified name. The new identifier is
  -- unique within the current scope. If no identifier can be generated for
  -- 'name', then 'Nothing' will be returned
  genIdent n env | SE.exists (Left  n) env = Nothing
                 | otherwise               = Just (try 0)
    where try i  | SE.exists (Right i) env = try (i + 1)
                 | otherwise               = renameIdent (mkIdent n) i

getModuleScope :: Module -> ScopeEnv
getModuleScope (Module _ _ ds) = foldr insertDecl SE.new ds

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

insertQIdent :: QualIdent -> ScopeEnv -> ScopeEnv
insertQIdent q = insertIdent (unqualify q)
