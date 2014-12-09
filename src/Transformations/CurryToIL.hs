{- |
    Module      :  $Header$
    Description :  Translation of Curry into IL
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                                   Martin Engelke
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After desugaring and lifting have been performed, the source code is
   translated into the intermediate language. Besides translating from
   source terms and expressions into intermediate language terms and
   expressions, this phase in particular has to implement the pattern
   matching algorithm for equations and case expressions.

   Because of name conflicts between the source and intermediate language
   data structures, we can use only a qualified import for the 'IL' module.
-}

module Transformations.CurryToIL (ilTrans, transType) where

import           Control.Monad               (liftM, liftM2)
import qualified Control.Monad.Reader as R
import           Data.List                   (nub, partition)
import qualified Data.Map             as Map (Map, empty, insert, lookup)
import qualified Data.Set             as Set (Set, empty, insert, delete, toList)

import Curry.Base.Position
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryTypes (toType)
import Base.Expr
import Base.Messages (internalError)
import Base.Types
import Base.Utils (foldr2, concatMapM)

import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

import qualified IL as IL

ilTrans :: Bool -> ValueEnv -> TCEnv -> Module -> IL.Module
ilTrans flat tyEnv tcEnv (Module _ m _ _ ds) = IL.Module m (imports m ds') ds'
  where ds' = R.runReader (concatMapM trDecl ds)
                          (TransEnv flat m tyEnv tcEnv)

transType :: ModuleIdent -> ValueEnv -> TCEnv -> Type -> IL.Type
transType m tyEnv tcEnv ty = R.runReader (trType ty)
                                         (TransEnv True m tyEnv tcEnv)

data TransEnv = TransEnv
  { flatTrans   :: Bool
  , moduleIdent :: ModuleIdent
  , valueEnv    :: ValueEnv
  , tyConsEnv   :: TCEnv
  }

type TransM a = R.Reader TransEnv a

isFlat :: TransM Bool
isFlat = R.asks flatTrans

getModuleIdent :: TransM ModuleIdent
getModuleIdent = R.asks moduleIdent

getValueEnv :: TransM ValueEnv
getValueEnv = R.asks valueEnv

getTCEnv :: TransM TCEnv
getTCEnv = R.asks tyConsEnv

trQualify :: Ident -> TransM QualIdent
trQualify i = getModuleIdent >>= \m -> return $ qualifyWith m i

-- Modules:
-- At the top-level, the compiler has to translate data type, newtype,
-- function, and external declarations. When translating a data type or
-- newtype declaration, we ignore the types in the declaration and lookup
-- the types of the constructors in the type environment instead because
-- these types are already fully expanded, i.e., they do not include any
-- alias types.

trDecl :: Decl -> TransM [IL.Decl]
trDecl (DataDecl    _ tc tvs cs _) = (:[]) `liftM` trData    tc tvs cs
trDecl (NewtypeDecl _ tc tvs nc _) = (:[]) `liftM` trNewtype tc tvs nc
trDecl (FunctionDecl  p _ _ f eqs) = (:[]) `liftM` trFunction  p f eqs
trDecl (ForeignDecl   _ cc ie f _) = (:[]) `liftM` trForeign  f cc ie
trDecl _                           = return []

trData :: Ident -> [Ident] -> [ConstrDecl] -> TransM IL.Decl
trData tc tvs cs = do
  tc' <- trQualify tc
  IL.DataDecl tc' (length tvs) `liftM` mapM trConstrDecl cs

trConstrDecl :: ConstrDecl -> TransM (IL.ConstrDecl [IL.Type])
trConstrDecl d = do
  c' <- trQualify (constr d)
  ty' <- arrowArgs `liftM` constrType c'
  IL.ConstrDecl c' `liftM` mapM trType ty'
  where
  constr (ConstrDecl    _ _ c _) = c
  constr (ConOpDecl  _ _ _ op _) = op

trNewtype :: Ident -> [Ident] -> NewConstrDecl -> TransM IL.Decl
trNewtype tc tvs (NewConstrDecl _ _ c _) = do
  tc' <- trQualify tc
  c'  <- trQualify c
  [ty] <- arrowArgs `liftM` constrType c'
  (IL.NewtypeDecl tc' (length tvs) . IL.ConstrDecl c') `liftM` trType ty

trForeign :: Ident -> CallConv -> Maybe String -> TransM IL.Decl
trForeign _ _  Nothing   = internalError "CurryToIL.trForeign: no target"
trForeign f cc (Just ie) = do
  f'  <- trQualify f
  ty' <- varType f' >>= trType
  return $ IL.ExternalDecl f' (callConv cc) ie ty'
  where
  callConv CallConvPrimitive = IL.Primitive
  callConv CallConvCCall     = IL.CCall

-- Interfaces:
-- In order to generate code, the compiler also needs to know the tags
-- and arities of all imported data constructors. For that reason we
-- compile the data type declarations of all interfaces into the
-- intermediate language, too. In this case we do not lookup the
-- types in the environment because the types in the interfaces are
-- already fully expanded. Note that we do not translate data types
-- which are imported into the interface from some other module.

-- ilTransIntf :: Interface -> TransM [IL.Decl]
-- ilTransIntf (Interface _ _ ds) = concatMapM translIntfDecl ds

-- translIntfDecl ::IDecl -> TransM [IL.Decl]
-- translIntfDecl (IDataDecl _ tc tvs cs)
--   | not (isQualified tc) = (:[]) `liftM`
--                            translIntfData (unqualify tc) tvs cs
-- translIntfDecl _         = return []

-- translIntfData :: Ident -> [Ident] -> [Maybe ConstrDecl] -> TransM IL.Decl
-- translIntfData tc tvs cs = do
--   tc' <- trQualify tc
--   cs' <- mapM (maybe (return hiddenConstr) (translIntfConstrDecl tvs)) cs
--   return $ IL.DataDecl tc' (length tvs) cs'
--   where hiddenConstr = IL.ConstrDecl (qualify anonId) []

-- translIntfConstrDecl :: [Ident] -> ConstrDecl
--                      -> TransM (IL.ConstrDecl [IL.Type])
-- translIntfConstrDecl tvs (ConstrDecl     _ _ c tys) = do
--   m <- getModuleIdent
--   c' <- trQualify c
--   IL.ConstrDecl c' `liftM` mapM trType (toQualTypes m tvs tys)
-- translIntfConstrDecl tvs (ConOpDecl _ _ ty1 op ty2) = do
--   m <- getModuleIdent
--   op' <- trQualify op
--   IL.ConstrDecl op' `liftM` mapM trType (toQualTypes m tvs [ty1, ty2])

-- Types:
-- The type representation in the intermediate language is the same as
-- the internal representation, except that it does not support
-- constrained type variables and skolem types. The former are fixed and
-- the later are replaced by fresh type constructors.

-- Due to possible occurrence of record types, it is necessary to transform
-- them back into their corresponding type constructors first.

trType :: Type -> TransM IL.Type
trType ty = trTy `liftM` elimRecordTypes (maximum $ 0 : typeVars ty) ty
  where
  trTy (TypeConstructor tc tys) = IL.TypeConstructor tc (map trTy tys)
  trTy (TypeVariable        tv) = IL.TypeVariable tv
  trTy (TypeConstrained  tys _) = trTy (head tys)
  trTy (TypeArrow      ty1 ty2) = IL.TypeArrow (trTy ty1) (trTy ty2)
  trTy (TypeSkolem           k) = IL.TypeConstructor
                                    (qualify (mkIdent ("_" ++ show k))) []
  trTy rec@(TypeRecord       _)
   = internalError $ "Translation of record not defined: " ++ show rec

elimRecordTypes :: Int -> Type -> TransM Type
elimRecordTypes n (TypeConstructor t tys)
  = TypeConstructor t `liftM` mapM (elimRecordTypes n) tys
elimRecordTypes _ v@(TypeVariable      _) = return v
elimRecordTypes n (TypeConstrained tys v)
  = flip TypeConstrained v `liftM` mapM (elimRecordTypes n) tys
elimRecordTypes n (TypeArrow       t1 t2)
  = liftM2 TypeArrow (elimRecordTypes n t1) (elimRecordTypes n t2)
elimRecordTypes _ s@(TypeSkolem        _) = return s
elimRecordTypes n (TypeRecord         fs)
  | null fs   = internalError "CurryToIL.elimRecordTypes: empty record type"
  | otherwise = do
    (r, n', fs') <- recordInfo (fst $ head fs)
    let vs  = foldl (matchTypeVars fs) Map.empty fs'
        tys = mapM (\i -> maybe (return $ TypeVariable (i+n))
                                (elimRecordTypes n)
                                (Map.lookup i vs))
                   [0 .. n'-1]
    TypeConstructor r `liftM` tys

matchTypeVars :: [(Ident, Type)] -> Map.Map Int Type -> (Ident, Type)
              -> Map.Map Int Type
matchTypeVars fs vs (l, ty) = maybe vs (match' vs ty) (lookup l fs)
  where
  match' vs' (TypeVariable        i) ty'
    = Map.insert i ty' vs'
  match' vs' (TypeConstructor _ tys) (TypeConstructor _ tys')
    = matchList vs' tys tys'
  match' vs' (TypeConstrained tys _) (TypeConstrained tys' _)
    = matchList vs' tys tys'
  match' vs' (TypeArrow     ty1 ty2) (TypeArrow    ty1' ty2')
    = matchList vs' [ty1,ty2] [ty1',ty2']
  match' vs' (TypeSkolem          _) (TypeSkolem           _) = vs'
  match' vs' (TypeRecord        fs1) (TypeRecord         fs2)
    = foldl (matchTypeVars fs2) vs' fs1
  match' _   ty1                     ty2
    = internalError ("CurryToIL.matchTypeVars: " ++ show ty1 ++ "\n" ++ show ty2)

  matchList vs1 tys tys' =
    foldl (\vs' (ty1,ty2) -> match' vs' ty1 ty2) vs1 (zip tys tys')

-- Functions:
-- Each function in the program is translated into a function of the
-- intermediate language. The arguments of the function are renamed such
-- that all variables occurring in the same position (in different
-- equations) have the same name. This is necessary in order to
-- facilitate the translation of pattern matching into a 'case' expression.
-- We use the following simple convention here: The top-level
-- arguments of the function are named from left to right '_1', '_2',
-- and so on. The names of nested arguments are constructed by appending
-- '_1', '_2', etc. from left to right to the name that were assigned
-- to a variable occurring at the position of the constructor term.

-- Some special care is needed for the selector functions introduced by
-- the compiler in place of pattern bindings. In order to generate the
-- code for updating all pattern variables, the equality of names between
-- the pattern variables in the first argument of the selector function
-- and their repeated occurrences in the remaining arguments must be
-- preserved. This means that the second and following arguments of a
-- selector function have to be renamed according to the name mapping
-- computed for its first argument.

-- If an evaluation annotation is available for a function, it determines
-- the evaluation mode of the case expression. Otherwise, the function
-- uses flexible matching.

trFunction :: Position -> Ident -> [Equation] -> TransM IL.Decl
trFunction p f eqs = do
  f' <- trQualify f
  ty' <- varType f' >>= trType
  flat <- isFlat
  let vs = if not flat && isFpSelectorId f then trArgs eqs funVars else funVars
  alts <-mapM (trEquation vs addVars) eqs
  let expr = flexMatch (srcRefOf p) vs alts
  return $ IL.FunctionDecl f' vs ty' expr
  where
  -- funVars are the variables needed for the function: _1, _2, etc.
  -- addVars is an infinite list for introducing additional variables later
  (funVars, addVars) = splitAt (equationArity (head eqs))
                               (argNames (mkIdent ""))
  equationArity (Equation _ lhs _) = p_equArity lhs
    where
    p_equArity (FunLhs _ ts) = length ts
    p_equArity (OpLhs _ _ _) = 2
    p_equArity _             = internalError "ILTrans - illegal equation"

-- TODO: What is this for?
trArgs :: [Equation] -> [Ident] -> [Ident]
trArgs [Equation _ (FunLhs _ (t:ts)) _] (v:_) =
  v : map (translArg (bindRenameEnv v t Map.empty)) ts
  where
    translArg env (VariablePattern v') = case Map.lookup v' env of
      Just x  -> x
      Nothing -> internalError "Transformations.CurryToIL.trArgs"
    translArg _ _ = internalError "Translation of arguments not defined"
trArgs _ _ = internalError "Translation of arguments not defined" -- TODO

trEquation :: [Ident]      -- identifiers for the function's parameters
           -> [Ident]      -- infinite list of additional identifiers
           -> Equation     -- equation to be translated
           -> TransM Match -- nested constructor terms + translated RHS
trEquation vs vs' (Equation _ (FunLhs _ ts) rhs) = do
  -- construct renaming of variables inside constructor terms
  let patternRenaming = foldr2 bindRenameEnv Map.empty vs ts
  -- translate right-hand-side
  rhs' <- trRhs vs' patternRenaming rhs
  -- convert patterns
  return (zipWith trPattern vs ts, rhs')
trEquation _  _    _
  = internalError "Translation of non-FunLhs euqation not defined"

trRhs :: [Ident] -> RenameEnv -> Rhs -> TransM IL.Expression
trRhs vs env (SimpleRhs _ e _) = trExpr vs env e
trRhs _  _   (GuardedRhs _  _) = internalError "CurryToIL.trRhs: GuardedRhs"

type RenameEnv = Map.Map Ident Ident

-- Construct a renaming of all variables inside the pattern
-- to fresh identifiers
bindRenameEnv :: Ident -> Pattern -> RenameEnv -> RenameEnv
bindRenameEnv _ (LiteralPattern        _) env = env
bindRenameEnv v (VariablePattern      v') env = Map.insert v' v env
bindRenameEnv v (ConstructorPattern _ ts) env
  = foldr2 bindRenameEnv env (argNames v) ts
bindRenameEnv v (AsPattern          v' t) env
  = Map.insert v' v (bindRenameEnv v t env)
bindRenameEnv _ _                         _   = internalError "CurryToIL.bindRenameEnv"

-- Expressions:
-- Note that the case matching algorithm assumes that the matched
-- expression is accessible through a variable. The translation of case
-- expressions therefore introduces a let binding for the scrutinized
-- expression and immediately throws it away after the matching -- except
-- if the matching algorithm has decided to use that variable in the
-- right hand sides of the case expression. This may happen, for
-- instance, if one of the alternatives contains an as-pattern.

trExpr :: [Ident] -> RenameEnv -> Expression -> TransM IL.Expression
trExpr _  _   (Literal     l) = return $ IL.Literal (trLiteral l)
trExpr _  env (Variable  _ v)
  | isQualified v = fun
  | otherwise     = case Map.lookup (unqualify v) env of
      Nothing -> fun
      Just v' -> return $ IL.Variable v' -- apply renaming
  where fun = (IL.Function v . arrowArity) `liftM` varType v
trExpr _  _   (Constructor c)
  = (IL.Constructor c . arrowArity) `liftM` constrType c
trExpr vs env (Apply   e1 e2)
  = liftM2 IL.Apply (trExpr vs env e1) (trExpr vs env e2)
trExpr vs env (Let      ds e) = do
  e' <- trExpr vs env' e
  case ds of
    [FreeDecl _ vs']
       -> return $ foldr IL.Exist e' vs'
    [d] | all (`notElem` bv d) (qfv emptyMIdent d)
      -> flip IL.Let    e' `liftM`      trBinding d
    _ -> flip IL.Letrec e' `liftM` mapM trBinding ds
  where
  env' = foldr2 Map.insert env bvs bvs
  bvs  = bv ds
  trBinding (PatternDecl _ _ _ (VariablePattern v) rhs)
    = IL.Binding v `liftM` trRhs vs env' rhs
  trBinding p = error $ "unexpected binding: " ++ show p
trExpr (v:vs) env (Case r ct e alts) = do
  -- the ident v is used for the case expression subject, as this could
  -- be referenced in the case alternatives by a variable pattern
  e' <- trExpr vs env e
  let matcher = if ct == Flex then flexMatch else rigidMatch
  expr <- matcher r [v] `liftM` mapM (trAlt (v:vs) env) alts
  return $ case expr of
    IL.Case r' mode (IL.Variable v') alts'
        -- subject is not referenced -> forget v and insert subject
      | v == v' && v `notElem` fv alts' -> IL.Case r' mode e' alts'
    _
        -- subject is referenced -> introduce binding for v as subject
      | v `elem` fv expr                -> IL.Let (IL.Binding v e') expr
      | otherwise                       -> expr
trExpr  vs env (Typed _ e _cx ty) =
  liftM2 IL.Typed (trExpr vs env e) (trType $ toType [] ty)
trExpr _ _ _ = internalError "CurryToIL.trExpr"

trAlt :: [Ident] -> RenameEnv -> Alt -> TransM Match
trAlt ~(v:vs) env (Alt _ t rhs) = do
  rhs' <- trRhs vs (bindRenameEnv v t env) rhs
  return ([trPattern v t], rhs')

data NestedTerm = NestedTerm IL.ConstrTerm [NestedTerm] deriving Show

pattern :: NestedTerm -> IL.ConstrTerm
pattern (NestedTerm t _) = t

arguments :: NestedTerm -> [NestedTerm]
arguments (NestedTerm _ ts) = ts

trLiteral :: Literal -> IL.Literal
trLiteral (Char      p c) = IL.Char p c
trLiteral (Int ident   i) = IL.Int (srcRefOf (idPosition ident)) i
trLiteral (Float ident f) = IL.Float (srcRefOf (idPosition ident)) f
trLiteral _             = internalError "CurryToIL.trLiteral"

trPattern :: Ident -> Pattern -> NestedTerm
trPattern _ (LiteralPattern        l)
  = NestedTerm (IL.LiteralPattern $ trLiteral l) []
trPattern v (VariablePattern       _) = NestedTerm (IL.VariablePattern v) []
trPattern v (ConstructorPattern c ts)
  = NestedTerm (IL.ConstructorPattern c (take (length ts) vs))
         (zipWith trPattern vs ts)
  where vs = argNames v
trPattern v (AsPattern           _ t) = trPattern v t
trPattern _ _                         = internalError "CurryToIL.trPattern"

argNames :: Ident -> [Ident]
argNames v = [mkIdent (prefix ++ show i) | i <- [1 :: Integer ..] ]
  where prefix = idName v ++ "_"

isVarPattern :: IL.ConstrTerm -> Bool
isVarPattern (IL.VariablePattern _) = True
isVarPattern _                      = False

isVarMatch :: (IL.ConstrTerm, a) -> Bool
isVarMatch = isVarPattern . fst

-- Pattern Matching:
-- The pattern matching code searches for the left-most inductive
-- argument position in the left hand sides of all rules defining an
-- equation. An inductive position is a position where all rules have a
-- constructor rooted term. If such a position is found, a 'case'
-- expression is generated for the argument at that position. The
-- matching code is then computed recursively for all of the alternatives
-- independently. If no inductive position is found, the algorithm looks
-- for the left-most demanded argument position, i.e., a position where
-- at least one of the rules has a constructor rooted term. If such a
-- position is found, an 'or' expression is generated with those
-- cases that have a variable at the argument position in one branch and
-- all other rules in the other branch. If there is no demanded position,
-- the pattern matching is finished and the compiler translates the right
-- hand sides of the remaining rules, eventually combining them using
-- 'or' expressions.

-- Actually, the algorithm below combines the search for inductive and
-- demanded positions. The function 'flexMatch' scans the argument
-- lists for the left-most demanded position. If this turns out to be
-- also an inductive position, the function 'flexMatchInductive' is
-- called in order to generate a 'case' expression. Otherwise, the
-- function 'optFlexMatch' is called that tries to find an inductive
-- position in the remaining arguments. If one is found,
-- 'flexMatchInductive' is called, otherwise the function
-- 'optFlexMatch' uses the demanded argument position found by 'flexMatch'.

-- a 'Match' is a list of patterns and the respective expression
type Match  = ([NestedTerm], IL.Expression)
-- a 'Match'' is a 'Match' with deferred patterns to be matched after
-- the next inductive position
type Match' = ([NestedTerm] -> [NestedTerm], [NestedTerm], IL.Expression)

flexMatch :: SrcRef       -- source reference
         -> [Ident]       -- new function variables
         -> [Match]       -- translated equations, list of: nested pattern+RHS
         -> IL.Expression -- result expression
flexMatch _ []     alts = foldl1 IL.Or (map snd alts)
flexMatch r (v:vs) alts
  | isInductive  = e1
  | notDemanded  = e2
  | otherwise    = optFlexMatch r (IL.Or e1 e2) (v:) vs (map skipArg alts)
  where
  isInductive       = null vars
  notDemanded       = null nonVars
  -- seperate variable and inductive patterns
  (vars, nonVars)   = partition isVarMatch (map tagAlt alts)
  e1                = flexMatchInductive r id v vs (map prep nonVars)
  -- match next variables
  e2                = flexMatch          r      vs (map snd vars)
  prep (p,(ts, e))  = (p, (id, ts, e))
  -- tagAlt extracts the constructor of the first pattern
  tagAlt  (t:ts, e) = (pattern t, (arguments t ++ ts, e))
  tagAlt  ([]  , _) = error "CurryToIL.flexMatch.tagAlt: empty list"
  -- skipArg skips the current argument for later matching
  skipArg (t:ts, e) = ((t:), ts, e)
  skipArg ([]  , _) = error "CurryToIL.flexMatch.skipArg: empty list"

optFlexMatch :: SrcRef              -- source reference
            -> IL.Expression        -- default expression
            -> ([Ident] -> [Ident]) -- variables to be matched next
            -> [Ident]              -- variables to be matched afterwards
            -> [Match']             -- translated equations, list of: nested pattern+RHS
            -> IL.Expression
-- if there are no variables left: return the default expression
optFlexMatch _ def _      []     _    = def
optFlexMatch r def prefix (v:vs) alts
  | isInductive = flexMatchInductive r prefix v vs alts'
  | otherwise   = optFlexMatch r def (prefix . (v:)) vs (map skipArg alts)
  where
  isInductive              = not (any isVarMatch alts')
  alts'                    = map tagAlt alts
  -- tagAlt extracts the next pattern and reinserts the skipped ones
  tagAlt  (pref, t:ts, e') = (pattern t, (pref, arguments t ++ ts, e'))
  tagAlt  (_   , []  , _ ) = error "CurryToIL.optFlexMatch.tagAlt: empty list"
  -- again, skipArg skips the current argument for later matching
  skipArg (pref, t:ts, e') = (pref . (t:), ts, e')
  skipArg (_   , []  , _ ) = error "CurryToIL.optFlexMatch.skipArg: empty list"

-- Generate a case expression matching the inductive position
flexMatchInductive :: SrcRef -> ([Ident] -> [Ident]) -> Ident
               -> [Ident] ->[(IL.ConstrTerm, Match')] -> IL.Expression
flexMatchInductive r prefix v vs as = IL.Case r IL.Flex (IL.Variable v) $
  flexMatchAlts as
  where
  -- create alternatives for the different constructors
  flexMatchAlts []              = []
  flexMatchAlts ((t, e) : alts) = IL.Alt t expr : flexMatchAlts others
    where
    -- match nested patterns for same constructors
    expr = flexMatch (srcRefOf t) (prefix $ vars t ++ vs) matchingCases
    matchingCases = map expandVars (e : map snd same)
    expandVars (pref, ts1, e') = (pref ts1, e')
    -- split into same and other constructors
    (same, others) = partition ((t ==) . fst) alts
    vars (IL.ConstructorPattern _ vs') = vs'
    vars _                             = []

-- Matching in a 'case'-expression works a little bit differently.
-- In this case, the alternatives are matched from the first to the last
-- alternative and the first matching alternative is chosen. All
-- remaining alternatives are discarded.

-- TODO: The case matching algorithm should use type information in order
-- to detect total matches and immediately discard all alternatives which
-- cannot be reached.

rigidMatch :: SrcRef -> [Ident] -> [Match] -> IL.Expression
rigidMatch r vs alts = rigidOptMatch r (snd $ head alts) id vs
                       (map prepare alts)
  where prepare (ts, e) = (id, ts, e)

rigidOptMatch :: SrcRef               -- source reference
              -> IL.Expression        -- default expression
              -> ([Ident] -> [Ident]) -- variables to be matched next
              -> [Ident]              -- variables to be matched afterwards
              -> [Match']             -- translated equations, list of: nested pattern+RHS
              -> IL.Expression
-- if there are no variables left: return the default expression
rigidOptMatch _ def _      []       _    = def
rigidOptMatch r def prefix (v : vs) alts
  | isInductive = rigidMatchInductive r prefix v vs alts'
  | otherwise   = rigidOptMatch r def (prefix . (v:)) vs (map skipArg alts)
  where
  isInductive              = not $ isVarMatch (head alts')
  alts'                    = map tagAlt alts
  -- tagAlt extracts the next pattern
  tagAlt  (pref, t:ts, e') = (pattern t, (pref, arguments t ++ ts, e'))
  tagAlt  (_   , []  , _ ) = error "CurryToIL.rigidOptMatch.tagAlt: empty list"
  -- skipArg skips the current argument for later matching
  skipArg (pref, t:ts, e') = (pref . (t:), ts, e')
  skipArg (_   , []  , _ ) = error "CurryToIL.rigidOptMatch.skipArg: empty list"

-- Generate a case expression matching the inductive position
rigidMatchInductive :: SrcRef -> ([Ident] -> [Ident]) -> Ident
                   -> [Ident] ->[(IL.ConstrTerm, Match')] -> IL.Expression
rigidMatchInductive r prefix v vs alts = IL.Case r IL.Rigid (IL.Variable v)
  $ map caseAlt (nonVarPats ++ varPats)
  where
  (varPats, nonVarPats) = partition isVarPattern $ nub $ map fst alts
  caseAlt t = IL.Alt t expr
    where
    expr = rigidMatch (srcRefOf t) (prefix $ vars t ++ vs) (matchingCases alts)
    -- matchingCases selects the matching branches and recursively
    -- matches the remaining patterns
    matchingCases = map (expandVars $ vars t) . filter (matches . fst)
    matches t' = t == t' || isVarPattern t'
    expandVars vs' (p, (pref, ts1, e)) = (pref ts2, e)
      where ts2 | isVarPattern p = map var2Pattern vs' ++ ts1
                | otherwise      = ts1
            var2Pattern v' = NestedTerm (IL.VariablePattern v') []
    vars (IL.ConstructorPattern _ vs') = vs'
    vars _                             = []

-- Auxiliary Definitions:
-- The functions 'varType' and 'constrType' return the type
-- of variables and constructors, respectively. The quantifiers are
-- stripped from the types.

varType :: QualIdent -> TransM Type
varType f = do
  tyEnv <- getValueEnv
  case qualLookupValue f tyEnv of
    [Value _ _ (ForAll _ _ ty) _] -> return ty
    _ -> internalError $ "CurryToIL.varType: " ++ show f

constrType :: QualIdent -> TransM Type
constrType c = do
  tyEnv <- getValueEnv
  case qualLookupValue c tyEnv of
    [DataConstructor  _ _ (ForAllExist _ _ _ ty)] -> return ty
    [NewtypeConstructor _ (ForAllExist _ _ _ ty)] -> return ty
    _ -> internalError $ "CurryToIL.constrType: " ++ show c

recordInfo :: Ident -> TransM (QualIdent, Int, [(Ident, Type)])
recordInfo f = do
  tyEnv <- getValueEnv
  case lookupValue f tyEnv of
    [Label _ r _] -> do
      tcEnv <- getTCEnv
      case qualLookupTC r tcEnv of
        [AliasType _ n (TypeRecord fs)] -> return (r, n, fs)
        _ -> internalError $ "CurryToIL.recordInfo: " ++ show f
    _ -> internalError $ "CurryToIL.recordInfo: " ++ show f

-- The list of import declarations in the intermediate language code is
-- determined by collecting all module qualifiers used in the current
-- module.

imports :: ModuleIdent -> [IL.Decl] -> [ModuleIdent]
imports m = Set.toList . Set.delete m . foldr mdlsDecl Set.empty

mdlsDecl :: IL.Decl -> Set.Set ModuleIdent -> Set.Set ModuleIdent
mdlsDecl (IL.DataDecl       _ _ cs) ms = foldr mdlsConstrsDecl ms cs
  where mdlsConstrsDecl (IL.ConstrDecl _ tys) ms' = foldr mdlsType ms' tys
mdlsDecl (IL.NewtypeDecl _ _ (IL.ConstrDecl _ ty)) ms = mdlsType ty ms
mdlsDecl (IL.FunctionDecl _ _ ty e) ms = mdlsType ty (mdlsExpr e ms)
mdlsDecl (IL.ExternalDecl _ _ _ ty) ms = mdlsType ty ms

mdlsType :: IL.Type -> Set.Set ModuleIdent -> Set.Set ModuleIdent
mdlsType (IL.TypeConstructor tc tys) ms = modules tc (foldr mdlsType ms tys)
mdlsType (IL.TypeVariable         _) ms = ms
mdlsType (IL.TypeArrow      ty1 ty2) ms = mdlsType ty1 (mdlsType ty2 ms)

mdlsExpr :: IL.Expression -> Set.Set ModuleIdent -> Set.Set ModuleIdent
mdlsExpr (IL.Function    f _) ms = modules f ms
mdlsExpr (IL.Constructor c _) ms = modules c ms
mdlsExpr (IL.Apply     e1 e2) ms = mdlsExpr e1 (mdlsExpr e2 ms)
mdlsExpr (IL.Case   _ _ e as) ms = mdlsExpr e (foldr mdlsAlt ms as)
  where
  mdlsAlt     (IL.Alt               t e') = mdlsPattern t . mdlsExpr e'
  mdlsPattern (IL.ConstructorPattern c _) = modules c
  mdlsPattern _                           = id
mdlsExpr (IL.Or        e1 e2) ms = mdlsExpr e1 (mdlsExpr e2 ms)
mdlsExpr (IL.Exist       _ e) ms = mdlsExpr e ms
mdlsExpr (IL.Let         b e) ms = mdlsBinding b (mdlsExpr e ms)
mdlsExpr (IL.Letrec     bs e) ms = foldr mdlsBinding (mdlsExpr e ms) bs
mdlsExpr _                    ms = ms

mdlsBinding :: IL.Binding -> Set.Set ModuleIdent -> Set.Set ModuleIdent
mdlsBinding (IL.Binding _ e) = mdlsExpr e

modules :: QualIdent -> Set.Set ModuleIdent -> Set.Set ModuleIdent
modules x ms = maybe ms (`Set.insert` ms) (qidModule x)
