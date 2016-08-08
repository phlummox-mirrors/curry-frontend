{- |
    Module      :  $Header$
    Description :  Generation of FlatCurry program and interface terms
    Copyright   :  (c) 2005       , Martin Engelke
                       2011 - 2016, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of a 'FlatCurry' program term
    for a given module in the intermediate language, and the generation
    of a 'FlatCurry' interface for a given 'Curry' interface.
-}
{-# LANGUAGE CPP #-}
module Generators.GenFlatCurry (genFlatCurry, genFlatInterface) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative        ((<$>), (<*>))
#endif
import           Control.Monad.Extra        (concatMapM)
import qualified Control.Monad.State as S   (State, evalState, gets, modify)
import           Data.Function              (on)
import           Data.List                  (nub, sort, sortBy)
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set (Set, empty, insert, member)

import           Curry.Base.Ident
import           Curry.Base.Position
import           Curry.ExtendedFlat.Goodies (funcName, opName, typeName)
import           Curry.ExtendedFlat.Type
import qualified Curry.Syntax as CS

import Base.CurryTypes     (toType)
import Base.Messages       (internalError)
import Base.NestEnv        ( NestEnv, emptyEnv, bindNestEnv, lookupNestEnv
                           , nestEnv, unnestEnv )
import Base.TypeExpansion
import Base.Types

import CompilerEnv
import Env.OpPrec          (mkPrec)
import Env.TypeConstructor (TCEnv)
import Env.Value           (ValueEnv, ValueInfo (..), qualLookupValue)

import qualified IL as IL
import Transformations     (transType)

-- transforms intermediate language code (IL) to FlatCurry code
genFlatCurry :: CompilerEnv -> CS.Module Type -> IL.Module -> Prog
genFlatCurry env mdl il = patchPrelude False $ run env mdl (trModule il)

-- transforms intermediate language code (IL) to FlatCurry interfaces
genFlatInterface :: CompilerEnv -> CS.Interface -> CS.Module Type -> IL.Module
                 -> Prog
genFlatInterface env i mdl (IL.Module _ is _)
  = patchPrelude True $ run env mdl (trInterface is i)

-- -----------------------------------------------------------------------------
-- Addition of primitive types for lists and tuples to the Prelude
-- -----------------------------------------------------------------------------

patchPrelude :: Bool -> Prog -> Prog
patchPrelude genInt p@(Prog n _ ts fs os)
  | n == prelude = Prog n [] ts' fs os
  | otherwise    = p
  where ts' = if genInt then sortBy (compare `on` typeName) pts else pts
        pts = primTypes ++ ts

primTypes :: [TypeDecl]
primTypes =
  [ Type arrow Public [0, 1] []
  , Type unit Public [] [(Cons unit 0 Public [])]
  , Type nil Public [0] [ Cons nil  0 Public []
                        , Cons cons 2 Public [TVar 0, TCons nil [TVar 0]]
                        ]
  ] ++ map mkTupleType [2 .. maxTupleArity]
  where arrow = mkPreludeQName "(->)"
        unit  = mkPreludeQName "()"
        nil   = mkPreludeQName "[]"
        cons  = mkPreludeQName ":"

mkTupleType :: Int -> TypeDecl
mkTupleType arity = Type tuple Public [0 .. arity - 1]
  [Cons tuple arity Public (map TVar [0 .. arity - 1])]
  where tuple = mkPreludeQName $ '(' : replicate (arity - 1) ',' ++ ")"

mkPreludeQName :: String -> QName
mkPreludeQName n = mkQName (prelude, n)

prelude :: String
prelude = "Prelude"

-- |Maximal arity of tuples
maxTupleArity :: Int
maxTupleArity = 15

-- -----------------------------------------------------------------------------

-- The environment 'FlatEnv' is embedded in the monadic representation
-- 'FlatState' which allows the usage of 'do' expressions.
type FlatState a = S.State FlatEnv a

-- Data type for representing an environment which contains information needed
-- for generating FlatCurry code.
data FlatEnv = FlatEnv
  { modIdent     :: ModuleIdent      -- current module
  -- for visibility calculation
  , tyExports    :: Set.Set Ident    -- exported types
  , valExports   :: Set.Set Ident    -- exported values (functions + constructors)
  , tcEnv        :: TCEnv            -- type constructor environment
  , tyEnv        :: ValueEnv         -- type environment
  , fixities     :: [CS.IDecl]       -- fixity declarations
  , typeSynonyms :: [CS.Decl Type]      -- type synonyms
  , imports      :: [ModuleIdent]    -- module imports
  -- state for mapping identifiers to indexes
  , nextVar      :: Int              -- fresh variable index counter
  , varMap       :: NestEnv VarIndex -- map of identifier to variable index
  }

-- Runs a 'FlatState' action and returns the result
run :: CompilerEnv -> CS.Module Type -> FlatState a -> a
run env (CS.Module _ mid es is ds) act = S.evalState act env0
  where
  es'  = case es of Just (CS.Exporting _ e) -> e
                    _                       -> []
  env0 = FlatEnv
    { modIdent     = mid
     -- for visibility calculation
    , tyExports  = foldr (buildTypeExports  mid) Set.empty es'
    , valExports = foldr (buildValueExports mid) Set.empty es'
    -- This includes *all* imports, even unused ones
    , imports      = nub [ m | CS.ImportDecl _ m _ _ _ <- is ]
    -- Environment to retrieve the type of identifiers
    , tyEnv        = valueEnv env
    , tcEnv        = tyConsEnv env
    -- Fixity declarations
    , fixities     = [ CS.IInfixDecl p fix (mkPrec mPrec) (qualifyWith mid o)
                     | CS.InfixDecl p fix mPrec os <- ds, o <- os
                     ]
    -- Type synonyms in the module
    , typeSynonyms = [ d | d@CS.TypeDecl{} <- ds ]
    , nextVar      = 0
    , varMap       = emptyEnv
    }

-- Builds a table containing all exported identifiers from a module.
buildTypeExports :: ModuleIdent -> CS.Export -> Set.Set Ident -> Set.Set Ident
buildTypeExports mid (CS.ExportTypeWith tc _)
  | isLocalIdent mid tc = Set.insert (unqualify tc)
buildTypeExports _   _  = id

-- Builds a table containing all exported identifiers from a module.
buildValueExports :: ModuleIdent -> CS.Export -> Set.Set Ident -> Set.Set Ident
buildValueExports mid (CS.Export             q)
  | isLocalIdent mid q  = Set.insert (unqualify q)
buildValueExports mid (CS.ExportTypeWith tc cs)
  | isLocalIdent mid tc = flip (foldr Set.insert) cs
buildValueExports _   _  = id

getModuleIdent :: FlatState ModuleIdent
getModuleIdent = S.gets modIdent

lookupType :: QualIdent -> FlatState (Maybe TypeExpr)
lookupType qid = S.gets tyEnv >>= \ env -> case qualLookupValue qid env of
  Value _ _ _ (ForAll _ (PredType _ t))                  : _ ->
    Just <$> trType (transType t)
  DataConstructor _ _ _ (ForAllExist _ _ (PredType _ t)) : _ ->
    Just <$> trType (transType t)
  _                                                          -> return Nothing

getArity :: QualIdent -> FlatState Int
getArity qid = S.gets tyEnv >>= \ env -> return $ case qualLookupValue qid env of
  [DataConstructor  _ a _ _] -> a
  [NewtypeConstructor _ _ _] -> 1
  [Value            _ _ a _] -> a
  [Label              _ _ _] -> 1
  _                          -> internalError
                                ("GenFlatCurry.getArity: " ++ qualName qid)

getFixities :: FlatState [CS.IDecl]
getFixities = S.gets fixities

-- The function 'typeSynonyms' returns the list of type synonyms.
getTypeSynonyms :: FlatState [CS.Decl Type]
getTypeSynonyms = S.gets typeSynonyms

-- Retrieve imports
getImports :: [ModuleIdent] -> FlatState [String]
getImports imps = (nub . map moduleName . (imps ++)) <$> S.gets imports

-- -----------------------------------------------------------------------------
-- Stateful part, used for translation of rules and expressions
-- -----------------------------------------------------------------------------

-- resets var index and environment
withFreshEnv :: FlatState a -> FlatState a
withFreshEnv act = S.modify (\ s -> s { nextVar = 0, varMap = emptyEnv }) >> act

-- Execute an action in a nested variable mapping
inNestedEnv :: FlatState a -> FlatState a
inNestedEnv act = do
  S.modify $ \ s -> s { varMap = nestEnv   $ varMap s }
  res <- act
  S.modify $ \ s -> s { varMap = unnestEnv $ varMap s }
  return res

-- Generates a new variable index for an identifier
newVar :: Ident -> FlatState VarIndex
newVar i = do
  ty  <- lookupType (qualify i)
  idx <- (+1) <$> S.gets nextVar
  let vid = VarIndex ty idx
  S.modify $ \ s -> s { nextVar = idx, varMap = bindNestEnv i vid (varMap s) }
  return vid

-- Retrieve the variable index assigned to an identifier
getVarIndex :: Ident -> FlatState VarIndex
getVarIndex i = S.gets varMap >>= \ varEnv -> case lookupNestEnv i varEnv of
  [v] -> return v
  _   -> internalError $ "GenFlatCurry.getVarIndex: " ++ escName i

-- -----------------------------------------------------------------------------
-- Translation of an interface
-- -----------------------------------------------------------------------------

trInterface :: [ModuleIdent] -> CS.Interface -> FlatState Prog
trInterface is (CS.Interface mid _ ds) = do
  is' <- getImports is
  tds <- concatMapM trITypeDecl ds
  lds <- concatMapM trLabelDecl ds
  fds <- concatMapM trIFuncDecl ds
  ops <- concatMapM trIOpDecl   ds
  return $ Prog (moduleName mid)
                (sort is')
                (sortBy (compare `on` typeName) tds)
                (sortBy (compare `on` funcName) (lds ++ fds))
                (sortBy (compare `on`   opName) ops)

trITypeDecl :: CS.IDecl -> FlatState [TypeDecl]
trITypeDecl (CS.IDataDecl _ qid _ tvs cs hs) = do
  mid <- getModuleIdent
  t'  <- trTypeIdent qid
  cs' <- mapM (trConsIDecl (fromMaybe mid $ qidModule qid) tvs)
         [c | c <- cs, CS.constrId c `notElem` hs]
  return [Type t' Public vs cs']
  where vs = [0 .. length tvs - 1]
trITypeDecl (CS.ITypeDecl _ qid _ tvs ty) = do
  t'  <- trTypeIdent qid
  ty' <- trType (transType $ toType tvs ty)
  return [TypeSyn t' Public vs ty']
  where vs = [0 .. length tvs - 1]
trITypeDecl _ = return []

trConsIDecl :: ModuleIdent -> [Ident] -> CS.ConstrDecl -> FlatState ConsDecl
trConsIDecl mid tvs (CS.ConstrDecl _ _ _ c tys) = do
  c'   <- trQIdent (qualifyWith mid c)
  tys' <- mapM (trType . transType . toType tvs) tys
  return (Cons c' (length tys) Public tys')
trConsIDecl mid tis (CS.ConOpDecl p vs cx ty1 op ty2) =
  trConsIDecl mid tis (CS.ConstrDecl p vs cx op [ty1, ty2])
trConsIDecl mid tis (CS.RecordDecl p vs cx c fs) =
  trConsIDecl mid tis (CS.ConstrDecl p vs cx c tys)
  where tys = [ty | CS.FieldDecl _ ls ty <- fs, _ <- ls]

-- Translate record types into label selector functions
trLabelDecl :: CS.IDecl -> FlatState [FuncDecl]
trLabelDecl (CS.IDataDecl _ qid _ tvs cs hs) = do
  mid <- getModuleIdent
  concatMapM (trLD mid) cs
  where
  trLD mid (CS.RecordDecl _ _ _ _ fs) = concatMapM trIFuncDecl
    [ CS.IFunctionDecl NoPos (qualifyWith mid l) False 1 (mkType ty)
    | CS.FieldDecl _ ls ty <- fs, l <- ls, l `notElem` hs
    ]
  trLD _   _                          = return []
  mkType = CS.QualTypeExpr [] . CS.ArrowType (foldl CS.ApplyType
                                                    (CS.ConstructorType qid)
                                                    (map CS.VariableType tvs))
trLabelDecl (CS.INewtypeDecl _ qid _ tvs nc hs) = do
  mid <- getModuleIdent
  trNC mid nc
  where
  trNC mid (CS.NewRecordDecl _ _ (l, ty))
    | l `notElem` hs =
      trIFuncDecl $ CS.IFunctionDecl NoPos (qualifyWith mid l) False 1 (mkType ty)
  trNC _   _                              = return []
  mkType = CS.QualTypeExpr [] . CS.ArrowType (foldl CS.ApplyType
                                                    (CS.ConstructorType qid)
                                                    (map CS.VariableType tvs))
trLabelDecl _ = return []

-- Translate an interface function declaration
trIFuncDecl :: CS.IDecl -> FlatState [FuncDecl]
trIFuncDecl (CS.IFunctionDecl _ f _ a (CS.QualTypeExpr _ ty)) = do
  f'  <- trQIdent f
  ty' <- trType $ transType $ toType [] ty
  return [Func f' a Public ty' (Rule [] (Var $ mkIdx 0))]
trIFuncDecl _ = return []

-- Translate an operator declaration
trIOpDecl :: CS.IDecl -> FlatState [OpDecl]
trIOpDecl (CS.IInfixDecl _ fix prec op)
  = (\op' -> [Op op' (cvFixity fix) prec]) <$> trQIdent op
trIOpDecl _ = return []

-- -----------------------------------------------------------------------------
-- Translation of a module
-- -----------------------------------------------------------------------------

trModule :: IL.Module -> FlatState Prog
trModule (IL.Module mid is ds) = do
  is' <- getImports is
  sns <- getTypeSynonyms >>= concatMapM trTypeSynonym
  tds <- concatMapM trTypeDecl ds
  fds <- concatMapM trFuncDecl ds
  ops <- getFixities     >>= concatMapM trIOpDecl
  return $ Prog (moduleName mid) is' (sns ++ tds) fds ops

-- Translate a type synonym
trTypeSynonym :: CS.Decl a -> FlatState [TypeDecl]
trTypeSynonym (CS.TypeDecl _ t tvs ty) = do
  m    <- getModuleIdent
  qid  <- flip qualifyWith t <$> getModuleIdent
  t'   <- trTypeIdent qid
  vis  <- getTypeVisibility qid
  tEnv <- S.gets tcEnv
  ty'  <- trType (transType $ expandType m tEnv $ toType tvs ty)
  return [TypeSyn t' vis [0 .. length tvs - 1] ty']
trTypeSynonym _                        = return []

-- Translate a data/newtype declaration
trTypeDecl :: IL.Decl -> FlatState [TypeDecl]
trTypeDecl (IL.DataDecl qid a cs) = do
  q'  <- trTypeIdent qid
  vis <-getTypeVisibility qid
  cs' <- mapM trConstrDecl cs
  return [Type q' vis [0 .. a - 1] cs']
trTypeDecl (IL.NewtypeDecl qid a (IL.ConstrDecl _ ty)) = do
  q'  <- trTypeIdent qid
  vis <- getTypeVisibility qid
  ty' <- trType ty
  return [TypeSyn q' vis [0 .. a - 1] ty']
trTypeDecl _ = return []

-- Translate a constructor declaration
trConstrDecl :: IL.ConstrDecl [IL.Type] -> FlatState ConsDecl
trConstrDecl (IL.ConstrDecl qid tys) = flip Cons (length tys)
  <$> trQIdent qid
  <*> getVisibility qid
  <*> mapM trType tys

-- Translate a type expression
trType :: IL.Type -> FlatState TypeExpr
trType (IL.TypeConstructor t tys) = TCons <$> trTypeIdent t <*> mapM trType tys
trType (IL.TypeVariable      idx) = return $ TVar $ abs idx
trType (IL.TypeArrow     ty1 ty2) = FuncType <$> trType ty1 <*> trType ty2

-- Convert a fixity
cvFixity :: CS.Infix -> Fixity
cvFixity CS.InfixL = InfixlOp
cvFixity CS.InfixR = InfixrOp
cvFixity CS.Infix  = InfixOp

-- -----------------------------------------------------------------------------
-- Function declarations
-- -----------------------------------------------------------------------------

-- Translate a function declaration
trFuncDecl :: IL.Decl -> FlatState [FuncDecl]
trFuncDecl (IL.FunctionDecl f vs ty e) = do
  f'  <- trQIdent f
  a   <- getArity f
  vis <- getVisibility f
  ty' <- trType ty
  r'  <- trRule vs e
  return [Func f' a vis ty' r']
trFuncDecl (IL.ExternalDecl  f _ e ty) = do
  f'   <- trQIdent f
  a    <- getArity f
  vis  <- getVisibility f
  ty'  <- trType ty
  r'   <- trExternal e
  return [Func f' a vis ty' r']
trFuncDecl _                           = return []

-- Translate a function rule.
-- Resets variable index so that for every rule variables start with index 1
trRule :: [Ident] -> IL.Expression -> FlatState Rule
trRule vs e = withFreshEnv $ Rule <$> mapM newVar vs <*> trExpr e

trExternal :: String -> FlatState Rule
trExternal e = do mid <- getModuleIdent
                  return (External $ moduleName mid ++ "." ++ e)

-- Translate an expression
trExpr :: IL.Expression -> FlatState Expr
trExpr (IL.Literal       l) = Lit <$> trLiteral l
trExpr (IL.Variable      v) = Var <$> getVarIndex v
trExpr (IL.Function    f _) = genCall Fun f []
trExpr (IL.Constructor c _) = genCall Con c []
trExpr (IL.Apply     e1 e2) = trApply e1 e2
trExpr (IL.Case   r t e bs) = Case r (cvEval t) <$> trExpr e
                              <*> mapM (inNestedEnv . trAlt) bs
trExpr (IL.Or        e1 e2) = Or <$> trExpr e1 <*> trExpr e2
trExpr (IL.Exist       v e) = inNestedEnv $ do
  v' <- newVar v
  e' <- trExpr e
  return $ case e' of Free vs e'' -> Free (v' : vs) e''
                      _           -> Free (v' : []) e'
trExpr (IL.Let (IL.Binding v b) e) = inNestedEnv $ do
  v' <- newVar v
  b' <- trExpr b
  e' <- trExpr e
  return $ case e' of Let bs e'' -> Let ((v', b'):bs) e''
                      _          -> Let ((v', b'):[]) e'
trExpr (IL.Letrec   bs e) = inNestedEnv $ do
  let (vs, es) = unzip [ (v, b) | IL.Binding v b <- bs]
  Let <$> (zip <$> mapM newVar vs <*> mapM trExpr es)
      <*> trExpr e
trExpr (IL.Typed e ty) = Typed <$> trExpr e <*> trType ty

-- Translate a literal
trLiteral :: IL.Literal -> FlatState Literal
trLiteral (IL.Char  rs c) = return $ Charc  rs c
trLiteral (IL.Int   rs i) = return $ Intc   rs i
trLiteral (IL.Float rs f) = return $ Floatc rs f

-- Translate a higher-order application
trApply :: IL.Expression -> IL.Expression -> FlatState Expr
trApply e1 e2 = genFlatApplic e1 [e2]
  where
  genFlatApplic e es = case e of
    IL.Apply     ea eb -> genFlatApplic ea (eb:es)
    IL.Function    f _ -> genCall Fun f es
    IL.Constructor c _ -> genCall Con c es
    _ -> do
      expr <- trExpr e
      genApply expr es

-- Translate an alternative
trAlt :: IL.Alt -> FlatState BranchExpr
trAlt (IL.Alt p e) = Branch <$> trPat p <*> trExpr e

-- Translate a pattern
trPat :: IL.ConstrTerm -> FlatState Pattern
trPat (IL.LiteralPattern        l) = LPattern <$> trLiteral l
trPat (IL.ConstructorPattern c vs) = Pattern  <$> trQIdent c <*> mapM newVar vs
trPat (IL.VariablePattern       _) = internalError "GenFlatCurry.trPat"

-- Convert a case type
cvEval :: IL.Eval -> CaseType
cvEval IL.Rigid = Rigid
cvEval IL.Flex  = Flex

data Call = Fun | Con

-- Generate a function or constructor call
genCall :: Call -> QualIdent -> [IL.Expression] -> FlatState Expr
genCall call f es = do
  f'    <- trQIdent f
  arity <- getArity f
  case compare supplied arity of
    LT -> genComb f' es (part call (arity - supplied))
    EQ -> genComb f' es (full call)
    GT -> do
      let (es1, es2) = splitAt arity es
      funccall <- genComb f' es1 (full call)
      genApply funccall es2
  where
  supplied = length es
  full Fun = FuncCall
  full Con = ConsCall
  part Fun = FuncPartCall
  part Con = ConsPartCall

genComb :: QName -> [IL.Expression] -> CombType -> FlatState Expr
genComb qid es ct = Comb ct qid <$> mapM trExpr es

genApply :: Expr -> [IL.Expression] -> FlatState Expr
genApply e es = do
  ap  <- trQIdent $ qualifyWith preludeMIdent (mkIdent "apply")
  es' <- mapM trExpr es
  return $ foldl (\e1 e2 -> Comb FuncCall ap [e1, e2]) e es'

-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

trQIdent :: QualIdent -> FlatState QName
trQIdent = trQualdent True

-- This variant of trQIdent does not look up the type of the identifier
trTypeIdent :: QualIdent -> FlatState QName
trTypeIdent = trQualdent False

trQualdent :: Bool -> QualIdent -> FlatState QName
trQualdent withType qid = do
  mid <- getModuleIdent
  mty <- if withType then lookupType qid else return Nothing
  return $ QName Nothing mty (moduleName $ fromMaybe mid mid') (idName i)
  where
  mid' | i `elem` [listId, consId, nilId, unitId] || isTupleId i
       = Just preludeMIdent
       | otherwise
       = qidModule qid
  i = qidIdent qid

getTypeVisibility :: QualIdent -> FlatState Visibility
getTypeVisibility i = S.gets $ \s ->
  if Set.member (unqualify i) (tyExports s) then Public else Private

getVisibility :: QualIdent -> FlatState Visibility
getVisibility i = S.gets $ \s ->
  if Set.member (unqualify i) (valExports s) then Public else Private
