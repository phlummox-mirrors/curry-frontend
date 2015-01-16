{- |
    Module      :  $Header$
    Description :  Lifting of lambda-expressions and local functions
    Copyright   :  (c) 2001 - 2003 Wolfgang Lux
                       2011 - 2015 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   After desugaring and simplifying the code, the compiler lifts all local
   function declarations to the top-level keeping only local variable
   declarations. The algorithm used here is similar to
   Johnsson's. It consists of two phases, first we abstract each local
   function declaration, adding its free variables as initial parameters
   and update all calls to take these variables into account.
   Then all local function declarations are collected and lifted to the
   top-level.
-}
{-# LANGUAGE CPP #-}
module Transformations.Lift (lift) where

#if __GLASGOW_HASKELL__ >= 710
import           Control.Applicative        ((<$>))
#else
import           Control.Applicative        ((<$>), (<*>))
#endif
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List
import qualified Data.Map            as Map (Map, empty, insert, lookup)
import qualified Data.Set            as Set (toList, fromList, unions)

import Curry.Base.Ident
import Curry.Syntax

import Base.Expr
import Base.Messages (internalError)
import Base.SCC
import Base.Types

import Env.Value

lift :: ValueEnv -> Module -> (Module, ValueEnv)
lift tyEnv (Module ps m es is ds) = (lifted, valueEnv s')
  where
  (ds', s') = S.runState (mapM (absDecl "" []) ds) initState
  initState = LiftState m tyEnv Map.empty
  lifted    = Module ps m es is $ concatMap liftFunDecl ds'

-- -----------------------------------------------------------------------------
-- Abstraction
-- -----------------------------------------------------------------------------

-- Besides adding the free variables to every (local) function, the
-- abstraction pass also has to update the type environment in order to
-- reflect the new types of the expanded functions. As usual, we use a
-- state monad transformer in order to pass the type environment
-- through. The environment constructed in the abstraction phase maps
-- each local function declaration onto its replacement expression,
-- i.e. the function applied to its free variables.

type AbstractEnv = Map.Map Ident (QualIdent, [Ident])

data LiftState = LiftState
  { moduleIdent :: ModuleIdent
  , valueEnv    :: ValueEnv
  , abstractEnv :: AbstractEnv
  }

type LiftM a = S.State LiftState a

getModuleIdent :: LiftM ModuleIdent
getModuleIdent = S.gets moduleIdent

getValueEnv :: LiftM ValueEnv
getValueEnv = S.gets valueEnv

modifyValueEnv :: (ValueEnv -> ValueEnv) -> LiftM ()
modifyValueEnv f = S.modify $ \ s -> s { valueEnv = f $ valueEnv s }

getAbstractEnv :: LiftM AbstractEnv
getAbstractEnv = S.gets abstractEnv

withLocalAbstractEnv :: AbstractEnv -> LiftM a -> LiftM a
withLocalAbstractEnv ae act = do
  old <- getAbstractEnv
  S.modify $ \ s -> s { abstractEnv = ae }
  res <- act
  S.modify $ \ s -> s { abstractEnv = old }
  return res

absDecl :: String -> [Ident] -> Decl -> LiftM Decl
absDecl _   lvs (FunctionDecl p f eqs) = FunctionDecl p f
                                         <$> mapM (absEquation lvs) eqs
absDecl pre lvs (PatternDecl  p t rhs) = PatternDecl  p t <$> absRhs pre lvs rhs
absDecl _   _   d                      = return d

absEquation :: [Ident] -> Equation -> LiftM Equation
absEquation lvs (Equation p lhs@(FunLhs f ts) rhs) =
  Equation p <$> absLhs lhs <*> absRhs (idName f ++ ".") (lvs ++ bv ts) rhs
absEquation _ _ = error "Lift.absEquation: no pattern match"

absLhs (FunLhs f ts) = FunLhs f <$> mapM absPattern ts

absRhs :: String -> [Ident] -> Rhs -> LiftM Rhs
absRhs pre lvs (SimpleRhs p e _) = flip (SimpleRhs p) [] <$> absExpr pre lvs e
absRhs _   _   _                 = error "Lift.absRhs: no simple RHS"

-- Within a declaration group we have to split the list of declarations
-- into the function and value declarations. Only the function
-- declarations are affected by the abstraction algorithm; the value
-- declarations are left unchanged except for abstracting their right
-- hand sides.

-- The abstraction of a recursive declaration group is complicated by the
-- fact that not all functions need to call each in a recursive
-- declaration group. E.g., in the following example neither 'g' nor 'h'
-- call each other.
--
--   f = g True
--     where x = f 1
--           f z = y + z
--           y = g False
--           g z = if z then x else 0
--
-- Because of this fact, f and g can be abstracted separately by adding
-- only 'y' to 'f' and 'x' to 'g'. On the other hand, in the following example
--
--   f x y = g 4
--     where g p = h p + x
--           h q = k + y + q
--           k = g x
--
-- the local function 'g' uses 'h', so the free variables
-- of 'h' have to be added to 'g' as well. However, because
-- 'h' does not call 'g' it is sufficient to add only
-- 'k' and 'y' (and not 'x') to its definition. We handle this by computing
-- the dependency graph between the functions and splitting this graph into
-- its strongly connected components. Each component is then processed
-- separately, adding the free variables in the group to its functions.

-- We have to be careful with local declarations within desugared case
-- expressions. If some of the cases have guards, e.g.,
--
--   case e of
--     x | x < 1 -> 1
--     x -> let double y = y * y in double x
--
-- the desugarer at present may duplicate code. While there is no problem
-- with local variable declaration being duplicated, we must avoid to
-- lift local function declarations more than once. Therefore
-- 'absFunDecls' transforms only those function declarations
-- that have not been lifted and discards the other declarations. Note
-- that it is easy to check whether a function has been lifted by
-- checking whether an entry for its untransformed name is still present
-- in the type environment.

absDeclGroup :: String -> [Ident] -> [Decl] -> Expression -> LiftM Expression
absDeclGroup pre lvs ds e = do
  m <- getModuleIdent
  absFunDecls pre (lvs ++ bv vds) (scc bv (qfv m) fds) vds e
  where (fds, vds) = partition isFunDecl ds

-- TODO: too complicated?
absFunDecls :: String -> [Ident] -> [[Decl]] -> [Decl] -> Expression
            -> LiftM Expression
absFunDecls pre lvs []         vds e = do
  vds' <- mapM (absDecl pre lvs) vds
  e' <- absExpr pre lvs e
  return (Let vds' e')
absFunDecls pre lvs (fds:fdss) vds e = do
  m   <- getModuleIdent
  env <- getAbstractEnv
  let fs     = bv fds
      fvs    = filter (`elem` lvs) (Set.toList fvsRhs)
      env'   = foldr (bindF fvs) env fs
      fvsRhs = Set.unions
          [ Set.fromList (maybe [v] (qfv m . asFunCall) (Map.lookup v env))
          | v <- qfv m fds]
      bindF fvs' f = Map.insert f (qualifyWith m $ liftIdent pre f, fvs')
      isLifted tyEnv f = null $ lookupValue f tyEnv
  fs' <- (\tyEnv -> filter (not . isLifted tyEnv) fs) <$> getValueEnv
  modifyValueEnv $ absFunTypes m pre fvs fs'
  (fds', e') <- withLocalAbstractEnv env' $ do
    fds'' <- mapM (absFunDecl pre fvs lvs)
               [d | d <- fds, any (`elem` fs') (bv d)]
    e''   <- absFunDecls pre lvs fdss vds e
    return (fds'', e'')
  return (Let fds' e')

absFunTypes :: ModuleIdent -> String -> [Ident] -> [Ident]
            -> ValueEnv -> ValueEnv
absFunTypes m pre fvs fs tyEnv = foldr abstractFunType tyEnv fs
  where tys = map (varType tyEnv) fvs
        abstractFunType f tyEnv' =
          qualBindFun m (liftIdent pre f)
                        (length fvs + varArity tyEnv' f) -- (arrowArity ty)
                        (polyType ty)
                        (unbindFun f tyEnv')
          where ty = foldr TypeArrow (varType tyEnv' f) tys

absFunDecl :: String -> [Ident] -> [Ident] -> Decl -> LiftM Decl
absFunDecl pre fvs lvs (FunctionDecl p f eqs) =
  absDecl pre lvs (FunctionDecl p f' (map (addVars f') eqs))
  where
  f' = liftIdent pre f
  addVars f1 (Equation p1 (FunLhs _ ts) rhs) =
          Equation p1 (FunLhs f1 (map VariablePattern fvs ++ ts)) rhs
  addVars _ _ = error "Lift.absFunDecl.addVars: no pattern match"
absFunDecl pre _   _  (ForeignDecl p cc ie f ty) =
  return $ ForeignDecl p cc ie (liftIdent pre f) ty
absFunDecl _ _ _ _ = error "Lift.absFunDecl: no pattern match"

absExpr :: String -> [Ident] -> Expression -> LiftM Expression
absExpr _   _   l@(Literal     _) = return l
absExpr pre lvs var@(Variable  v)
  | isQualified v = return var
  | otherwise     = do
    getAbstractEnv >>= \env -> case Map.lookup (unqualify v) env of
      Nothing -> return var
      Just v' -> absExpr pre lvs (asFunCall v')
absExpr _   _   c@(Constructor _) = return c
absExpr pre lvs (Apply     e1 e2) = Apply         <$> absExpr pre lvs e1
                                                  <*> absExpr pre lvs e2
absExpr pre lvs (Let        ds e) = absDeclGroup pre lvs ds e
absExpr pre lvs (Case  r ct e bs) = Case r ct     <$> absExpr pre lvs e
                                                  <*> mapM (absAlt pre lvs) bs
absExpr pre lvs (Typed      e ty) = flip Typed ty <$> absExpr pre lvs e
absExpr _   _   e                 = internalError $ "Lift.absExpr: " ++ show e

absAlt :: String -> [Ident] -> Alt -> LiftM Alt
absAlt pre lvs (Alt p t rhs) = Alt p t <$> absRhs pre (lvs ++ bv t) rhs

absPattern :: Pattern -> LiftM Pattern
absPattern v@(VariablePattern _) = return v
absPattern l@(LiteralPattern  _) = return l
absPattern (ConstructorPattern c ps) = ConstructorPattern c <$> mapM absPattern ps
absPattern (AsPattern v p) = AsPattern v <$> absPattern p
absPattern (FunctionPattern f ps) = do
  getAbstractEnv >>= \env -> case Map.lookup (unqualify f) env of
    Nothing       -> FunctionPattern f  <$> mapM absPattern ps
    Just (f', vs) -> (FunctionPattern f' . (map VariablePattern vs ++))
                     <$> mapM absPattern ps
absPattern _ = error "Lift.absPattern"

-- -----------------------------------------------------------------------------
-- Lifting
-- -----------------------------------------------------------------------------

-- After the abstraction pass, all local function declarations are lifted
-- to the top-level.

liftFunDecl :: Decl -> [Decl]
liftFunDecl (FunctionDecl p f eqs) = (FunctionDecl p f eqs' : concat dss')
  where (eqs', dss') = unzip $ map liftEquation eqs
liftFunDecl d                      = [d]

liftVarDecl :: Decl -> (Decl, [Decl])
liftVarDecl (PatternDecl   p t rhs) = (PatternDecl p t rhs', ds')
  where (rhs', ds') = liftRhs rhs
liftVarDecl ex@(FreeDecl _ _) = (ex, [])
liftVarDecl _ = error "Lift.liftVarDecl: no pattern match"

liftEquation :: Equation -> (Equation, [Decl])
liftEquation (Equation p lhs rhs) = (Equation p lhs rhs', ds')
  where (rhs', ds') = liftRhs rhs

liftRhs :: Rhs -> (Rhs, [Decl])
liftRhs (SimpleRhs p e _) = (SimpleRhs p e' [], ds')
  where (e', ds') = liftExpr e
liftRhs _ = error "Lift.liftRhs: no pattern match"

liftDeclGroup :: [Decl] -> ([Decl],[Decl])
liftDeclGroup ds = (vds', concat $ map liftFunDecl fds ++ dss')
  where (fds , vds ) = partition isFunDecl ds
        (vds', dss') = unzip $ map liftVarDecl vds

liftExpr :: Expression -> (Expression, [Decl])
liftExpr l@(Literal      _) = (l, [])
liftExpr v@(Variable     _) = (v, [])
liftExpr c@(Constructor  _) = (c, [])
liftExpr (Apply      e1 e2) = (Apply e1' e2', ds' ++ ds'')
  where (e1', ds' ) = liftExpr e1
        (e2', ds'') = liftExpr e2
liftExpr (Let         ds e) = (mkLet ds' e', ds'' ++ ds''')
  where (ds', ds'' ) = liftDeclGroup ds
        (e' , ds''') = liftExpr e
        mkLet ds1 e1 = if null ds1 then e1 else Let ds1 e1
liftExpr (Case r ct e alts) = (Case r ct e' alts', concat $ ds' : dss')
  where (e'   ,ds' ) = liftExpr e
        (alts',dss') = unzip $ map liftAlt alts
liftExpr (Typed       e ty) = (Typed e' ty, ds) where (e', ds) = liftExpr e
liftExpr _ = internalError "Lift.liftExpr"

liftAlt :: Alt -> (Alt, [Decl])
liftAlt (Alt p t rhs) = (Alt p t rhs', ds') where (rhs', ds') = liftRhs rhs

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

isFunDecl :: Decl -> Bool
isFunDecl (FunctionDecl     _ _ _) = True
isFunDecl (ForeignDecl  _ _ _ _ _) = True
isFunDecl _                        = False

asFunCall :: (QualIdent, [Ident]) -> Expression
asFunCall (f, vs) = apply (Variable f) (map mkVar vs)

mkFun :: ModuleIdent -> String -> Ident -> Expression
mkFun m pre f = Variable $ qualifyWith m $ liftIdent pre f

mkVar :: Ident -> Expression
mkVar v = Variable $ qualify v

apply :: Expression -> [Expression] -> Expression
apply = foldl Apply

varArity :: ValueEnv -> Ident -> Int
varArity tyEnv v = case lookupValue v tyEnv of
  [Value _ a _] -> a
  _ -> internalError $ "Lift.varArity: " ++ show v

varType :: ValueEnv -> Ident -> Type
varType tyEnv v = case lookupValue v tyEnv of
  [Value _ _ (ForAll _ ty)] -> ty
  _ -> internalError $ "Lift.varType: " ++ show v

liftIdent :: String -> Ident -> Ident
liftIdent prefix x = renameIdent (mkIdent $ prefix ++ showIdent x)
                   $ idUnique x
