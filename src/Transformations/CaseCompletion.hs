{- |CaseCompletion - expands case branches with missing constructors

    The MMC translates case expressions into the intermediate language
    representation (IL) without completing them (i.e. without generating
    case branches for missing contructors). Because they are necessary for
    the PAKCS back end, this module expands all case expressions accordingly.

    May 2005, Martin Engelke, (men@informatik.uni-kiel.de)
-}
module Transformations.CaseCompletion (completeCase) where

import Prelude hiding (mod)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)

import Curry.Base.Ident
import Curry.Base.Position (SrcRef)
import qualified Curry.Syntax as CS

import Env.Interface (InterfaceEnv, lookupInterface)
import IL

type Message = String

-- Completes case expressions by adding branches for missing constructors.
-- The interface environment 'menv' is needed to compute these constructors.
completeCase :: InterfaceEnv -> Module -> Module
completeCase iEnv mdl = fst $ visitModule iEnv mdl

-- ---------------------------------------------------------------------------
-- The following functions traverse an IL term searching for case expressions
type CCM a = Module -> InterfaceEnv -> [Message] -> ScopeEnv -> a -> (a, [Message], ScopeEnv)

visitModule :: InterfaceEnv -> Module -> (Module, [Message])
visitModule iEnv mdl@(Module mid is ds) = (Module mid is ds', msgs')
 where (ds', msgs', _) = visitList visitDecl insertDeclScope mdl iEnv
                         []
                         (getModuleScope mdl)
                         ds

visitDecl :: CCM Decl
visitDecl _    _    msgs senv dd@(DataDecl        _ _ _) = (dd, msgs, senv)
visitDecl _    _    msgs senv nt@(NewtypeDecl     _ _ _) = (nt, msgs, senv)
visitDecl mod1 menv msgs senv (FunctionDecl qid vs ty e)
  = (FunctionDecl qid vs ty e', msgs, senv)
  where (e', _, _) = visitExpr mod1 menv msgs (insertExprScope senv e) e
visitDecl _    _    msgs senv ed@(ExternalDecl  _ _ _ _) = (ed, msgs, senv)

visitExpr :: CCM Expression
visitExpr _    _    msgs senv l@(Literal       _) = (l, msgs, senv)
visitExpr _    _    msgs senv v@(Variable      _) = (v, msgs, senv)
visitExpr _    _    msgs senv f@(Function    _ _) = (f, msgs, senv)
visitExpr _    _    msgs senv c@(Constructor _ _) = (c, msgs, senv)
visitExpr mod1 menv msgs senv (Apply       e1 e2) = (Apply e1' e2', m2, s2)
 where
  (e1', m1, s1) = visitExpr mod1 menv msgs (insertExprScope senv e1) e1
  (e2', m2, s2) = visitExpr mod1 menv m1   (insertExprScope s1   e2) e2

visitExpr mod1 menv msgs senv (Case r ea e alts)
  | null altsR        = intError "visitExpr" "empty alternative list"
    -- pattern matching causes flexible case expressions
  | ea == Flex       = (Case r ea e' altsR, msgs, senv1)
  | isConstrAlt altR = (expr2, msgs3, senv3)
  | isLitAlt    altR = (completeLitAlts r ea e' altsR, msgs3, senv2)
  | isVarAlt    altR = (completeVarAlts e' altsR, msgs3, senv2)
  | otherwise        = intError "visitExpr" "illegal alternative list"
  where
  (e'   , _, senv1) = visitExpr mod1 menv msgs (insertExprScope senv e) e
  (alts', _, senv2) = visitList visitAlt insertAltScope mod1 menv msgs senv1 alts
  (altsR, msgs3) = removeRedundantAlts msgs alts'
  (expr2, senv3) = completeConsAlts r mod1 menv senv2 ea e' altsR
  altR           = head altsR

visitExpr mod menv msgs senv (Or e1 e2) = (Or e1' e2', msgs2, senv3)
  where
  (e1', msgs1, senv2) = visitExpr mod menv msgs  (insertExprScope senv e1) e1
  (e2', msgs2, senv3) = visitExpr mod menv msgs1 (insertExprScope senv2 e2) e2

visitExpr mod menv msgs senv (Exist v e) = (Exist v e', msgs', senv2)
  where (e', msgs', senv2) = visitExpr mod menv msgs (insertExprScope senv e) e

visitExpr mod menv msgs senv (Let b e) = (Let b' e', msgs2, senv3)
  where
  (e', _    , senv2) = visitExpr mod menv msgs (insertExprScope senv e) e
  (b', msgs2, senv3) = visitBinding mod menv msgs (insertBindingScope senv2 b) b

visitExpr mod menv msgs senv (Letrec bs e) = (Letrec bs' e', msgs2, senv3)
  where
  (e' , msgs1, senv2) = visitExpr mod menv msgs (insertExprScope senv e) e
  (bs', msgs2, senv3) = visitList visitBinding const mod menv
                          msgs1
                          (foldl insertBindingScope senv2 bs)
                          bs

visitAlt :: CCM Alt
visitAlt mod menv msgs senv (Alt p e) = (Alt p e', msgs', senv')
  where (e', msgs', senv') = visitExpr mod menv msgs (insertExprScope senv e) e

visitBinding :: CCM Binding
visitBinding mod menv msgs senv (Binding ident e)
  = (Binding ident e', msgs', senv2)
  where
  (e', msgs', senv2) = visitExpr mod menv msgs (insertExprScope senv e) e

visitList :: CCM a -> (ScopeEnv -> a -> ScopeEnv) -> CCM [a]
visitList _   _      _   _    msgs senv []     = ([]      , msgs, senv)
visitList act fScope mdl iEnv msgs senv (t:ts) = ((t':ts'), msgs2, senv3)
 where (t' , msgs1, senv2) = act mdl iEnv msgs (fScope senv t) t
       (ts', msgs2, senv3) = visitList act fScope mdl iEnv msgs1 senv2 ts

-- ---------------------------------------------------------------------------
-- Functions for completing case alternatives

-- Completes a case alternative list which branches via constructor patterns
-- by adding alternatives of the form
--
--      comp_pattern -> default_expr
--
-- where "comp_pattern" is a complementary constructor pattern and
-- "default_expr" is the expression from the first alternative containing
-- a variable pattern. If there is no such alternative the defualt expression
-- is set to the prelude function 'failed'.
--
-- This funtions uses a scope environment ('ScopeEnv') to generate fresh
-- variables for the arguments of the new constructors.
--
completeConsAlts :: SrcRef -> Module -> InterfaceEnv -> ScopeEnv
		    -> Eval -> Expression -> [Alt]
		    -> (Expression, ScopeEnv)
completeConsAlts r mod menv senv evalannot expr alts
   = (Case r evalannot expr (alts1 ++ alts2), senv2)
 where
   (Alt varpatt defaultexpr) = getDefaultAlt alts
   (VariablePattern varid)   = varpatt
   alts1       = filter isConstrAlt alts
   constrs     = (map p_getConsAltIdent alts1)
   cconsinfos  = getComplConstrs mod menv constrs
   (cconstrs,senv2) =
                 foldr p_genConstrTerm
                       ([],senv)
                       cconsinfos
   alts2       = map (\cconstr ->
		      (Alt cconstr
		        (replaceVar varid (cterm2expr cconstr) defaultexpr)))
		     cconstrs

   p_getConsAltIdent (Alt (ConstructorPattern qident _) _) = qident
   p_getConsAltIdent _ = error
     "CaseCompletion.completeConsAlts.p_getConsAltIdent: no pattern match"

   p_genConstrTerm (qident, arity) (cconstrs1,senv3) =
       let args = genIdentList arity "x" senv3
           senv4 = foldr insertIdent senv3 args
       in (ConstructorPattern qident args : cconstrs1, senv4)

-- If the alternatives branches via literal pattern complementary
-- constructor list cannot be generated because it would become infinite.
-- So the function 'completeLitAlts' transforms case expressions like
--      case <cexpr> of
--        <lit_1> -> <expr_1>
--        <lit_2> -> <expr_2>
--                    :
--        <lit_n> -> <expr_n>
--       [<var>   -> <default_expr>]
-- to
--      case (<cexpr> == <lit_1>) of
--        True  -> <expr_1>
--        False -> case (<cexpr> == <lit_2>) of
--                   True  -> <expr_2>
--                   False -> case ...
--                                  :
--                               -> case (<cexpr> == <lit_n>) of
--                                    True  -> <expr_n>
--                                    False -> <default_expr>
--
completeLitAlts :: SrcRef -> Eval -> Expression -> [Alt] -> Expression
completeLitAlts _ _         _    [] = failedExpr
completeLitAlts r evalannot expr (alt:alts)
  | isLitAlt alt = (Case r evalannot
                    (eqExpr expr (p_makeLitExpr alt))
                    [(Alt truePatt  (getAltExpr alt)),
                      (Alt falsePatt (completeLitAlts r evalannot expr alts))])
  | otherwise = case alt of
    Alt (VariablePattern v) expr' -> replaceVar v expr expr'
    _ -> intError "completeLitAlts" "illegal alternative"
 where
   p_makeLitExpr alt1
      = case (getAltPatt alt1) of
	  LiteralPattern lit -> Literal lit
	  _                  -> intError "completeLitAlts"
				         "literal pattern expected"

-- For the unusual case of having only one alternative containing a variable
-- pattern it is necessary to tranform it to a 'let' term because FlatCurry
-- does not support variable patterns in case alternatives. So the
-- case expression
--      case <ce> of
--        x -> <expr>
-- is transformed ot
--      let x = <ce> in <expr>
completeVarAlts :: Expression -> [Alt] -> Expression
completeVarAlts _    [] = failedExpr
completeVarAlts expr (alt:_)
  = (Let (Binding (p_getVarIdent alt) expr) (getAltExpr alt))
  where
  p_getVarIdent alt' = case getAltPatt alt' of
    VariablePattern ident -> ident
    _                     -> intError "completeVarAlts" "variable pattern expected"

-------------------------------------------------------------------------------
-- The function 'removeRedundantAlts' removes case branches which are
-- either idle (i.e. they will never be reached) or multiply declared.
-- Note: unlike the PAKCS frontend MCC does not support warnings. So
-- there will be no messages if alternatives have been removed.

removeRedundantAlts :: [Message] -> [Alt] -> ([Alt], [Message])
removeRedundantAlts msgs alts = (alts2, msgs2)
  where (alts1, msgs1) = removeIdleAlts msgs alts
        (alts2, msgs2) = removeMultipleAlts msgs1 alts1

-- An alternative is idle if it occurs anywhere behind another alternative
-- which contains a variable pattern. Example:
--    case x of
--      (y:ys) -> e1
--      z      -> e2
--      []     -> e3
-- Here all alternatives behind (z  -> e2) are idle and will be removed.
removeIdleAlts :: [Message] -> [Alt] -> ([Alt], [Message])
removeIdleAlts msgs alts
  | null alts2 = (alts1, msgs)
  | otherwise  = (alts1, msgs)
  where (alts1, alts2) = splitAfter isVarAlt alts

-- An alternative occurs multiply if at least two alternatives
-- use the same pattern. Example:
--    case x of
--      []     -> e1
--      (y:ys) -> e2
--      []     -> e3
-- Here the last alternative occures multiply because its pattern is already
-- used in the first alternative. All multiple alternatives will be
-- removed except for the first occurrence.
removeMultipleAlts :: [Message] -> [Alt] -> ([Alt], [Message])
removeMultipleAlts msgs alts = p_remove msgs [] alts
  where
  p_remove msgs1 altsR []      = (reverse altsR, msgs1)
  p_remove msgs1 altsR (alt1:alts1)
    | p_containsAlt alt1 altsR = p_remove msgs1 altsR alts1
    | otherwise                = p_remove msgs1 (alt1:altsR) alts1

  p_containsAlt alt' alts' = any (p_eqAlt alt') alts'

  p_eqAlt (Alt (LiteralPattern lit1) _) alt2 = case alt2 of
    (Alt (LiteralPattern lit2) _) -> lit1 == lit2
    _                             -> False
  p_eqAlt (Alt (ConstructorPattern qident1 _) _) alt2 = case alt2 of
    (Alt (ConstructorPattern qident2 _) _) -> qident1 == qident2
    _                                      -> False
  p_eqAlt (Alt (VariablePattern _) _) alt2 = case alt2 of
    (Alt (VariablePattern _) _) -> True
    _                           -> False

-- ---------------------------------------------------------------------------
-- Some functions for testing and extracting terms from case alternatives

isVarAlt :: Alt -> Bool
isVarAlt (Alt (VariablePattern _) _) = True
isVarAlt _                           = False

isConstrAlt :: Alt -> Bool
isConstrAlt (Alt (ConstructorPattern _ _) _) = True
isConstrAlt _                                = False

isLitAlt :: Alt -> Bool
isLitAlt (Alt (LiteralPattern _) _) = True
isLitAlt _                          = False

getAltExpr :: Alt -> Expression
getAltExpr (Alt _ e) = e

getAltPatt :: Alt -> ConstrTerm
getAltPatt (Alt p _) = p

-- Note: the newly generated variable 'x!' is just a dummy and will never
-- occur in the transformed program
getDefaultAlt :: [Alt] -> Alt
getDefaultAlt alts
   = fromMaybe (Alt (VariablePattern (mkIdent "x!")) failedExpr)
               (find isVarAlt alts)

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
replaceVar v e (Apply     e1 e2) = Apply (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Case r ev e' bs) = Case r ev (replaceVar v e e')
                                             (map (replaceVarInAlt v e) bs)
replaceVar v e (Or        e1 e2) = Or (replaceVar v e e1) (replaceVar v e e2)
replaceVar v e (Exist      w e')
   | v == w    = Exist w e'
   | otherwise = Exist w (replaceVar v e e')
replaceVar v e (Let       bd e')
   | varOccursInBinding v bd = Let bd e'
   | otherwise               = Let (replaceVarInBinding v e bd)
                                   (replaceVar v e e')
replaceVar v e (Letrec    bs e')
   | any (varOccursInBinding v) bs = Letrec bs e'
   | otherwise                     = Letrec (map (replaceVarInBinding v e) bs)
                                            (replaceVar v e e')
replaceVar _ _ e' = e'

replaceVarInAlt :: Ident -> Expression -> Alt -> Alt
replaceVarInAlt v e (Alt p e')
  | varOccursInPattern v p = Alt p e'
  | otherwise              = Alt p (replaceVar v e e')

replaceVarInBinding :: Ident -> Expression -> Binding -> Binding
replaceVarInBinding v e (Binding w e')
  | v == w    = Binding w e'
  | otherwise = Binding w (replaceVar v e e')

varOccursInPattern :: Ident -> ConstrTerm -> Bool
varOccursInPattern v (VariablePattern       w) = v == w
varOccursInPattern v (ConstructorPattern _ vs) = v `elem` vs
varOccursInPattern _ _                         = False

varOccursInBinding :: Ident -> Binding -> Bool
varOccursInBinding v (Binding w _) = v == w

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

cterm2expr :: ConstrTerm -> Expression
cterm2expr (LiteralPattern            l) = Literal l
cterm2expr (VariablePattern           v) = Variable v
cterm2expr (ConstructorPattern qid args)
  = p_genApplic (Constructor qid (length args)) args
  where
  p_genApplic e []     = e
  p_genApplic e (v:vs) = p_genApplic (Apply e (Variable v)) vs

-------------------------------------------------------------------------------
-- The folowing functions compute the missing constructors for generating
-- new case alternatives

-- Computes the complementary constructors for a list of constructors. All
-- specified constructors must have the same type.
-- This functions uses the module environment 'menv' which contains all known
-- constructors, except for those which are declared in the module and
-- except for the list constructors.
getComplConstrs :: Module -> InterfaceEnv -> [QualIdent] -> [(QualIdent, Int)]
getComplConstrs (Module mid _ decls) menv constrs
  | null constrs
  = intError "getComplConstrs" "empty constructor list"
  | cons == qNilId || cons == qConsId
  = getCC constrs [(qNilId, 0), (qConsId, 2)]
  | mid' == mid
  = getCCFromDecls mid constrs decls
  | otherwise
  = maybe [] (getCCFromIDecls mid' constrs) (lookupInterface mid' menv)
  where
  cons = head constrs
  mid' = fromMaybe mid (qidModule cons)

-- Find complementary constructors within the declarations of the
-- current module
getCCFromDecls :: ModuleIdent -> [QualIdent] -> [Decl] -> [(QualIdent, Int)]
getCCFromDecls _ constrs decls = getCC constrs cinfos
  where
  cdecls = maybe [] p_extractConstrDecls
           (find (p_declaresConstr (head constrs)) decls)
  cinfos = map p_getConstrDeclInfo cdecls

  p_declaresConstr qid decl = case decl of
    DataDecl _ _ cs    -> any (p_isConstrDecl qid) cs
    NewtypeDecl _ _ nc -> p_isConstrDecl qid nc
    _                  -> False

  p_isConstrDecl qident (ConstrDecl qid _) = qident == qid

  p_extractConstrDecls decl = case decl of
    DataDecl _ _ cs   -> cs
    _                 -> []

  p_getConstrDeclInfo (ConstrDecl qident types) = (qident, length types)

-- Find complementary constructors within the module environment
getCCFromIDecls :: ModuleIdent -> [QualIdent] -> CS.Interface -> [(QualIdent, Int)]
getCCFromIDecls mid constrs (CS.Interface _ _ ds) = getCC constrs cinfos
  where
  cdecls = maybe [] p_extractIConstrDecls
           (find (p_declaresIConstr (head constrs)) ds)
  cinfos = map p_getIConstrDeclInfo cdecls

  p_declaresIConstr qid idecl = case idecl of
    CS.IDataDecl    _ _ _ cs -> any (p_isIConstrDecl qid) $ catMaybes cs
    CS.INewtypeDecl _ _ _ nc -> p_isINewConstrDecl qid nc
    _                        -> False

  p_isIConstrDecl qid (CS.ConstrDecl  _ _ cid _) = unqualify qid == cid
  p_isIConstrDecl qid (CS.ConOpDecl _ _ _ oid _) = unqualify qid == oid

  p_isINewConstrDecl qid (CS.NewConstrDecl _ _ cid _) = unqualify qid == cid

  p_extractIConstrDecls idecl = case idecl of
    CS.IDataDecl _ _ _ cs -> catMaybes cs
    _                     -> []

  p_getIConstrDeclInfo (CS.ConstrDecl _ _ cid tys)
    = (qualifyWith mid cid, length tys)
  p_getIConstrDeclInfo (CS.ConOpDecl  _ _ _ oid _)
    = (qualifyWith mid oid, 2)

-- Compute complementary constructors
getCC :: [QualIdent] -> [(QualIdent, Int)] -> [(QualIdent, Int)]
getCC _  []                 = []
getCC cs (ci@(qid,_) : cis)
  | any (== qid) cs = getCC cs cis
  | otherwise       = ci: getCC cs cis

-- ---------------------------------------------------------------------------
-- Miscellaneous

-- Splits a list behind the first element which satifies 'p'
splitAfter :: (a -> Bool) -> [a] -> ([a], [a])
splitAfter p xs = p_splitAfter p [] xs
  where
  p_splitAfter _ fs []                 = (reverse fs    , [])
  p_splitAfter c fs (l:ls) | c l       = (reverse (l:fs), ls)
                           | otherwise = p_splitAfter c (l:fs) ls

-- Returns the first element which satisfy 'cond'. The returned element is
-- embedded in a 'Maybe' term
find :: (a -> Bool) -> [a] -> Maybe a
find _ []     = Nothing
find p (x:xs) | p x       = Just x
              | otherwise = find p xs

-- Raises an internal error
intError :: String -> String -> a
intError fun msg = error ("CaseCompletion." ++ fun ++ " - " ++ msg)

-- 2011-02-08 (bjp): Moved from IL.Scope

getModuleScope :: Module -> ScopeEnv
getModuleScope (Module _ _ ds) = foldl insertDecl newScopeEnv ds

insertDeclScope :: ScopeEnv -> Decl -> ScopeEnv
insertDeclScope env (DataDecl        _ _ _) = env
insertDeclScope env (NewtypeDecl     _ _ _) = env
insertDeclScope env (FunctionDecl _ vs _ _) = foldr insertIdent (beginScope env) vs
insertDeclScope env (ExternalDecl  _ _ _ _) = env

insertExprScope :: ScopeEnv -> Expression -> ScopeEnv
insertExprScope env (Literal       _) = env
insertExprScope env (Variable      _) = env
insertExprScope env (Function    _ _) = env
insertExprScope env (Constructor _ _) = env
insertExprScope env (Apply       _ _) = env
insertExprScope env (Case    _ _ _ _) = env
insertExprScope env (Or          _ _) = env
insertExprScope env (Exist       v _) = insertIdent v (beginScope env)
insertExprScope env (Let         b _) = insertBinding (beginScope env) b
insertExprScope env (Letrec     bs _) = foldl insertBinding (beginScope env) bs

insertAltScope :: ScopeEnv -> Alt -> ScopeEnv
insertAltScope env (Alt p _) = insertConstrTerm (beginScope env) p

insertBindingScope :: ScopeEnv -> Binding -> ScopeEnv
insertBindingScope env _ = env

insertDecl :: ScopeEnv -> Decl -> ScopeEnv
insertDecl env (DataDecl      qid _ cs)
  = foldl insertConstrDecl (insertIdent (unqualify qid) env) cs
insertDecl env (NewtypeDecl    qid _ c)
  = insertConstrDecl (insertIdent (unqualify qid) env) c
insertDecl env (FunctionDecl qid _ _ _) = insertIdent (unqualify qid) env
insertDecl env (ExternalDecl qid _ _ _) = insertIdent (unqualify qid) env

insertConstrDecl :: ScopeEnv -> ConstrDecl a -> ScopeEnv
insertConstrDecl env (ConstrDecl qid _) = insertIdent (unqualify qid) env

insertConstrTerm :: ScopeEnv -> ConstrTerm -> ScopeEnv
insertConstrTerm env (LiteralPattern        _) = env
insertConstrTerm env (ConstructorPattern _ vs) = foldr insertIdent env vs
insertConstrTerm env (VariablePattern       v) = insertIdent v env

insertBinding :: ScopeEnv -> Binding -> ScopeEnv
insertBinding env (Binding v _) = insertIdent v env

-- ---------------------------------------------------------------------------
-- ScopeEnv stuff - Moved from Base.OldScopeEnv on 2012-09-04
-- ---------------------------------------------------------------------------

-- The IdEnv is an environment which stores the level in which an identifier
-- was defined, starting with 0 for the top-level.
data IdRep = Name String | Index Integer deriving (Eq, Ord)
type IdEnv = Map.Map IdRep Integer

insertId :: Integer -> Ident -> IdEnv -> IdEnv
insertId level ident = Map.insert (Name  (idName   ident)) level
                     . Map.insert (Index (idUnique ident)) level

nameExists :: String -> IdEnv -> Bool
nameExists name = Map.member (Name name)

indexExists :: Integer -> IdEnv -> Bool
indexExists index = Map.member (Index index)

genId :: String -> IdEnv -> Maybe Ident
genId n env
   | nameExists n env = Nothing
   | otherwise        = Just (p_genId (mkIdent n) 0)
 where
   p_genId ident index
      | indexExists index env = p_genId ident (index + 1)
      | otherwise             = renameIdent ident index

-- Type for representing an environment containing identifiers in several
-- scope levels
type ScopeLevel = Integer
type ScopeEnv   = (IdEnv, [IdEnv], ScopeLevel)
-- (top-level IdEnv, stack of lower level IdEnv, current level)
-- Invariant: The current level is the number of stack elements

-- Generates a new instance of a scope table
newScopeEnv :: ScopeEnv
newScopeEnv = (Map.empty, [], 0)

-- Insert an identifier into the current level of the scope environment
insertIdent :: Ident -> ScopeEnv -> ScopeEnv
insertIdent ident (topleveltab, leveltabs, level) = case leveltabs of
  []       -> ((insertId level ident topleveltab), [], 0)
  (lt:lts) -> (topleveltab, (insertId level ident lt) : lts, level)

-- Increase the level of the scope.
beginScope :: ScopeEnv -> ScopeEnv
beginScope (topleveltab, leveltabs, level) = case leveltabs of
  []       -> (topleveltab, [Map.empty], 1)
  (lt:lts) -> (topleveltab, (lt:lt:lts), level + 1)

-- Generates a list of new identifiers where each identifier has
-- the prefix 'name' followed by  an index (i.e. "var3" if 'name' was "var").
-- All returned identifiers are unique within the current scope.
genIdentList :: Int -> String -> ScopeEnv -> [Ident]
genIdentList size name scopeenv = p_genIdentList size name scopeenv 0
  where
  p_genIdentList :: Int -> String -> ScopeEnv -> Int -> [Ident]
  p_genIdentList s n env i
    | s == 0    = []
    | otherwise = maybe (p_genIdentList s n env (i + 1))
                        (\ident -> ident:(p_genIdentList (s - 1)
                        n
                        (insertIdent ident env)
                        (i + 1)))
                        (genIdent (n ++ (show i)) env)

-- Generates a new identifier for the specified name. The new identifier is
-- unique within the current scope. If no identifier can be generated for
-- 'name' then 'Nothing' will be returned
genIdent :: String -> ScopeEnv -> Maybe Ident
genIdent name (topleveltab, leveltabs, _) = case leveltabs of
  []     -> genId name topleveltab
  (lt:_) -> genId name lt

-- OLD STUFF

-- -- Return the declaration level of an identifier if it exists
-- getIdentLevel :: Ident -> ScopeEnv -> Maybe Integer
-- getIdentLevel ident (topleveltab, leveltabs, _) = case leveltabs of
--   []     -> getIdLevel ident topleveltab
--   (lt:_) -> maybe (getIdLevel ident topleveltab) Just (getIdLevel ident lt)

-- -- Checkswhether the specified identifier is visible in the current scope
-- -- (i.e. check whether the identifier occurs in the scope environment)
-- isVisible :: Ident -> ScopeEnv -> Bool
-- isVisible ident (topleveltab, leveltabs, _) = case leveltabs of
--   []     -> idExists ident topleveltab
--   (lt:_) -> idExists ident lt || idExists ident topleveltab
--
-- -- Check whether the specified identifier is declared in the
-- -- current scope (i.e. checks whether the identifier occurs in the
-- -- current level of the scope environment)
-- isDeclared :: Ident -> ScopeEnv -> Bool
-- isDeclared ident (topleveltab, leveltabs, level) = case leveltabs of
--   []     -> maybe False ((==) 0) (getIdLevel ident topleveltab)
--   (lt:_) -> maybe False ((==) level) (getIdLevel ident lt)

-- -- Decrease the level of the scope. Identifier from higher levels
-- -- will be lost.
-- endScope :: ScopeEnv -> ScopeEnv
-- endScope (topleveltab, leveltabs, level) = case leveltabs of
--   []      -> (topleveltab, [], 0)
--   (_:lts) -> (topleveltab, lts, level - 1)

-- -- Return the level of the current scope. Top level is 0
-- getLevel :: ScopeEnv -> ScopeLevel
-- getLevel (_, _, level) = level

-- idExists :: Ident -> IdEnv -> Bool
-- idExists ident = indexExists (uniqueId ident)

-- getIdLevel :: Ident -> IdEnv -> Maybe Integer
-- getIdLevel ident = Map.lookup (Index (uniqueId ident))
