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
   declarations. The algorithm used here is similar to Johnsson's, consisting
   of two phases. First, we abstract each local function declaration,
   adding its free variables as initial parameters and update all calls
   to take these variables into account. Second, all local function
   declarations are collected and lifted to the top-level.
-}
{-# LANGUAGE CPP #-}
module Transformations.Lift (lift) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Arrow              (first)
import qualified Control.Monad.State as S   (State, runState, gets, modify)
import           Data.List
import qualified Data.Map            as Map (Map, empty, insert, lookup)
import qualified Data.Set            as Set (toList, fromList, unions)

import Curry.Base.Ident
import Curry.Base.Position                  (Position)
import Curry.Syntax

import Base.Expr
import Base.Messages                        (internalError)
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

absLhs :: Lhs -> LiftM Lhs
absLhs (FunLhs f ts) = FunLhs f <$> mapM absPat ts
absLhs _             = error "Lift.absLhs: no simple LHS"

absRhs :: String -> [Ident] -> Rhs -> LiftM Rhs
absRhs pre lvs (SimpleRhs p e _) = simpleRhs p <$> absExpr pre lvs e
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
--     where x = h 1
--           h z = y + z
--           y = g False
--           g z = if z then x else 0
--
-- Because of this fact, 'g' and 'h' can be abstracted separately by adding
-- only 'y' to 'h' and 'x' to 'g'. On the other hand, in the following example
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

absFunDecls :: String -> [Ident] -> [[Decl]] -> [Decl] -> Expression
            -> LiftM Expression
absFunDecls pre lvs []         vds e = do
  vds' <- mapM (absDecl pre lvs) vds
  e' <- absExpr pre lvs e
  return (Let vds' e')
absFunDecls pre lvs (fds:fdss) vds e = do
  m     <- getModuleIdent
  env   <- getAbstractEnv
  tyEnv <- getValueEnv
  let -- defined functions
      fs     = bv fds
      -- free variables on the right-hand sides
      fvsRhs = Set.unions
          [ Set.fromList (maybe [v] (qfv m . asFunCall) (Map.lookup v env))
          | v <- qfv m fds]
      -- free variables that are local
      fvs    = filter (`elem` lvs) (Set.toList fvsRhs)
      -- extended abstraction environment
      env'   = foldr (bindF fvs) env fs
      bindF fvs' f = Map.insert f (qualifyWith m $ liftIdent pre f, fvs')
      -- newly abstracted functions
      fs'    = filter (\f -> not $ null $ lookupValue f tyEnv) fs
  -- update environment
  modifyValueEnv $ absFunTypes m pre fvs fs'
  withLocalAbstractEnv env' $ do
    -- add variables to functions
    fds' <- mapM (absFunDecl pre fvs lvs) [d | d <- fds, any (`elem` fs') (bv d)]
    -- abstract remaining declarations
    e'   <- absFunDecls pre lvs fdss vds e
    return (Let fds' e')

-- Add the additional variables to the types of the functions and rebind
-- the functions in the value environment
absFunTypes :: ModuleIdent -> String -> [Ident] -> [Ident]
            -> ValueEnv -> ValueEnv
absFunTypes m pre fvs fs tyEnv = foldr abstractFunType tyEnv fs
  where tys = map (varType tyEnv) fvs
        abstractFunType f tyEnv' =
          qualBindFun m (liftIdent pre f)
                        (length fvs + varArity tyEnv' f)
                        (polyType (normType ty))
                        (unbindFun f tyEnv')
          where ty = foldr TypeArrow (varType tyEnv' f) tys

normType :: Type -> Type
normType ty = norm (zip (nub $ typeVars ty) [0..]) ty
  where
  norm vs (TypeVariable n) = case lookup n vs of
    Just m  -> TypeVariable m
    Nothing -> error "Lift.normType"
  norm vs (TypeConstructor tc tys) = TypeConstructor tc (map (norm vs) tys)
  norm vs (TypeArrow      ty1 ty2) = TypeArrow (norm vs ty1) (norm vs ty2)
  norm _  tc@(TypeConstrained _ _) = tc
  norm _  tsk@(TypeSkolem       _) = tsk

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

-- TODO: Remove since functional patterns should not be abstracted

absPat :: Pattern -> LiftM Pattern
absPat v@(VariablePattern     _) = return v
absPat l@(LiteralPattern      _) = return l
absPat (ConstructorPattern c ps) = ConstructorPattern c <$> mapM absPat ps
absPat (AsPattern           v p) = AsPattern v <$> absPat p
absPat (FunctionPattern    f ps) = do
  getAbstractEnv >>= \env -> case Map.lookup (unqualify f) env of
    Nothing       -> FunctionPattern f  <$> mapM absPat ps
    Just (f', vs) -> (FunctionPattern f' . (map VariablePattern vs ++))
                     <$> mapM absPat ps
absPat p = error $ "Lift.absPat: " ++ show p

-- -----------------------------------------------------------------------------
-- Lifting
-- -----------------------------------------------------------------------------

-- After the abstraction pass, all local function declarations are lifted
-- to the top-level.

liftFunDecl :: Decl -> [Decl]
liftFunDecl (FunctionDecl p f eqs) = FunctionDecl p f eqs' : concat dss'
  where (eqs', dss') = unzip $ map liftEquation eqs
liftFunDecl d                      = [d]

liftVarDecl :: Decl -> (Decl, [Decl])
liftVarDecl (PatternDecl   p t rhs) = (PatternDecl p t rhs', ds')
  where (rhs', ds') = liftRhs rhs
liftVarDecl ex@(FreeDecl       _ _) = (ex, [])
liftVarDecl _ = error "Lift.liftVarDecl: no pattern match"

liftEquation :: Equation -> (Equation, [Decl])
liftEquation (Equation p lhs rhs) = (Equation p lhs rhs', ds')
  where (rhs', ds') = liftRhs rhs

liftRhs :: Rhs -> (Rhs, [Decl])
liftRhs (SimpleRhs p e _) = first (simpleRhs p) (liftExpr e)
liftRhs _                 = error "Lift.liftRhs: no pattern match"

liftDeclGroup :: [Decl] -> ([Decl],[Decl])
liftDeclGroup ds = (vds', concat (map liftFunDecl fds ++ dss'))
  where (fds , vds ) = partition isFunDecl ds
        (vds', dss') = unzip $ map liftVarDecl vds

liftExpr :: Expression -> (Expression, [Decl])
liftExpr l@(Literal      _) = (l, [])
liftExpr v@(Variable     _) = (v, [])
liftExpr c@(Constructor  _) = (c, [])
liftExpr (Apply      e1 e2) = (Apply e1' e2', ds1 ++ ds2)
  where (e1', ds1) = liftExpr e1
        (e2', ds2) = liftExpr e2
liftExpr (Let         ds e) = (mkLet ds' e', ds1 ++ ds2)
  where (ds', ds1) = liftDeclGroup ds
        (e' , ds2) = liftExpr e
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

mkVar :: Ident -> Expression
mkVar v = Variable $ qualify v

mkLet :: [Decl] -> Expression -> Expression
mkLet ds e = if null ds then e else Let ds e

apply :: Expression -> [Expression] -> Expression
apply = foldl Apply

simpleRhs :: Position -> Expression -> Rhs
simpleRhs p e = SimpleRhs p e []

varArity :: ValueEnv -> Ident -> Int
varArity tyEnv v = case lookupValue v tyEnv of
  [Value _ a _] -> a
  _ -> internalError $ "Lift.varArity: " ++ show v

varType :: ValueEnv -> Ident -> Type
varType tyEnv v = case lookupValue v tyEnv of
  [Value _ _ (ForAll _ ty)] -> ty
  _ -> internalError $ "Lift.varType: " ++ show v

liftIdent :: String -> Ident -> Ident
liftIdent prefix x = renameIdent (mkIdent $ prefix ++ showIdent x) $ idUnique x
