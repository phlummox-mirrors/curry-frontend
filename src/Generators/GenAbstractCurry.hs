{- |
    Module      :  $Header$
    Description :  Generation of AbstractCurry program terms
    Copyright   :  (c) 2005         Martin Engelke
                       2011 - 2014  Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of an 'AbstractCurry' program term
    for a given 'Curry' module.
-}
module Generators.GenAbstractCurry
  ( genTypedAbstract, genUntypedAbstract ) where

import           Prelude hiding             (mapM)

import           Control.Monad hiding       (forM, mapM)
import qualified Control.Monad.State as S
import           Data.List                  (find)
import qualified Data.Map            as Map
import           Data.Maybe                 (fromMaybe)
import qualified Data.Set            as Set
import           Data.Traversable

import Curry.AbstractCurry
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryTypes (fromType)
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types
import Base.Utils (concatMapM)

import Env.TypeConstructor (TCEnv, lookupTC)
import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

import CompilerEnv

-- -----------------------------------------------------------------------------
-- Interface
-- -----------------------------------------------------------------------------

-- |Generate type inferred AbstractCurry code from a Curry module.
--  The function needs the type environment 'tyEnv' to determine the
--  inferred function types.
genTypedAbstract :: CompilerEnv -> Module -> CurryProg
genTypedAbstract = genAbstract TypedAcy

-- |Generate untyped AbstractCurry code from a Curry module. The type
--  signature takes place in every function type annotation, if it exists,
--  otherwise the dummy type "Prelude.untyped" is used.
genUntypedAbstract :: CompilerEnv -> Module -> CurryProg
genUntypedAbstract = genAbstract UntypedAcy

-- |Generate an AbstractCurry program term from the syntax tree
genAbstract :: AbstractType -> CompilerEnv -> Module -> CurryProg
genAbstract ty env mdl = S.evalState (genModule mdl) (abstractEnv ty env mdl)

-- -----------------------------------------------------------------------------
-- This part defines an environment containing all necessary information
-- for generating the AbstractCurry representation of a CurrySyntax term.
-- -----------------------------------------------------------------------------

-- |Data type for representing an AbstractCurry generator environment
data AbstractEnv = AbstractEnv
  { acyType    :: AbstractType               -- ^ type of code to be generated
  , moduleId   :: ModuleIdent                -- ^ name of the module
  , exports    :: Set.Set Ident              -- ^ exported symbols
  , typeEnv    :: ValueEnv                   -- ^ known values
  , tconsEnv   :: TCEnv                      -- ^ known type constructors
  , varIndex   :: Int                        -- ^ next fresh variable
  , tvarIndex  :: Int                        -- ^ next fresh type variable
  , varScope   :: [Map.Map Ident CVarIName ] -- ^ stack of variable tables
  , tvarScope  :: [Map.Map Ident CTVarIName] -- ^ stack of type variable tables
  } deriving Show

-- |Data type representing the type of AbstractCurry code to be generated
-- (typed infered or untyped (i.e. type signated))
data AbstractType
  = TypedAcy
  | UntypedAcy
    deriving (Eq, Show)

-- |Initialize the AbstractCurry generator environment
abstractEnv :: AbstractType -> CompilerEnv -> Module -> AbstractEnv
abstractEnv absType env (Module _ mid es _ ds) = AbstractEnv
  { acyType   = absType
  , moduleId  = mid
  , typeEnv   = valueEnv  env
  , tconsEnv  = tyConsEnv env
  , exports   = buildExportSet mid ds
              $ maybe [ExportModule mid] (\ (Exporting _ specs) -> specs) es
  , varIndex  = 0
  , tvarIndex = 0
  , varScope  = [Map.empty]
  , tvarScope = [Map.empty]
  }

-- Builds a table containing all exported (public) identifiers from a module.
buildExportSet :: ModuleIdent -> [Decl] -> [Export] -> Set.Set Ident
buildExportSet mid ds = foldl build Set.empty
  where
  build :: Set.Set Ident -> Export -> Set.Set Ident
  build s (Export             qid)
    | isLocalIdent mid qid = Set.insert (unqualify qid) s
    | otherwise            = s
  build s (ExportTypeWith qid ids)
    | isLocalIdent mid qid = foldl (flip Set.insert) s (unqualify qid : ids)
    | otherwise            = s
  build s (ExportTypeAll      qid) = case localIdent mid qid of
    Just i -> foldl (flip Set.insert) s (i : getConstructors i ds)
    Nothing    -> s
  build s (ExportModule  mid2)
    | mid == mid2 = foldl build s (genExports ds)
    | otherwise   = s

  getConstructors :: Ident -> [Decl] -> [Ident]
  getConstructors i = concatMap get
    where
    get (DataDecl _ j _ cs) | i == j = map getConstr cs
    get _                            = []

    getConstr (ConstrDecl  _ _  c _) = c
    getConstr (ConOpDecl _ _ _ op _) = op

  -- Generates a list of exports for all specified top level declarations.
  genExports :: [Decl] -> [Export]
  genExports = concatMap export
    where
    export (DataDecl       _ i _ _) = [ExportTypeAll (qualifyWith mid i)]
    export (NewtypeDecl    _ i _ _) = [ExportTypeAll (qualifyWith mid i)]
    export (TypeDecl       _ i _ _) = [Export        (qualifyWith mid i)]
    export (FunctionDecl     _ i _) = [Export        (qualifyWith mid i)]
    export (ForeignDecl  _ _ _ i _) = [Export        (qualifyWith mid i)]
    export (ExternalDecl      _ is) = map (Export . qualifyWith mid) is
    export _                        = []

-- -----------------------------------------------------------------------------
-- State access
-- -----------------------------------------------------------------------------

type Gen a = S.State AbstractEnv a

getAcyType :: Gen AbstractType
getAcyType = S.gets acyType

getModuleIdent :: Gen ModuleIdent
getModuleIdent = S.gets moduleId

-- | Check whether an identifier is exported or not.
isExported :: Ident -> Gen Bool
isExported ident = S.gets $ Set.member ident . exports

-- Looks up the type of a qualified symbol in the type environment
-- and converts it to a CurrySyntax type term.
qualLookupType :: QualIdent -> Gen (Maybe TypeExpr)
qualLookupType qid = S.gets $ \ s -> case qualLookupValue qid (typeEnv s) of
  [Value _ _ (ForAll _ ty)] -> Just $ fromType ty
  _                         -> Nothing

lookupTypeName :: QualIdent -> Gen QualIdent
lookupTypeName qid = S.gets $ \ s -> case lookupTC ident (tconsEnv s) of
  [info] -> origName info
  _      -> qid
  where ident = unqualify qid

lookupValueName :: QualIdent -> Gen QualIdent
lookupValueName qid = S.gets $ \ s -> case lookupValue ident (typeEnv s) of
  [info] -> origName info
  _      -> qid
  where ident = unqualify qid

-- Generates an unique index for the  variable 'ident' and inserts it
-- into the  variable table of the current scope.
genVar :: Ident -> Gen CVarIName
genVar i = do
  s <- S.get
  let idx = varIndex s
      v   = (idx, conIdent i)
  S.put $ s { varIndex = idx + 1
            , varScope = Map.insert i v `mapStack` varScope s }
  return v

-- Looks up the unique index for the variable 'ident' in the
-- variable table of the current scope.
lookupVar :: Ident -> Gen (Maybe CVarIName)
lookupVar ident = S.gets $ Map.lookup ident . topStack . varScope

-- Generates an unique index for the type variable 'ident' and inserts it
-- into the type variable table of the current scope.
genTVar :: Ident -> Gen CTVarIName
genTVar i = do
  s <- S.get
  let idx = tvarIndex s
      tv  = (idx, conIdent i)
  S.put $ s { tvarIndex = idx + 1
            , tvarScope = Map.insert i tv `mapStack` tvarScope s }
  return tv

-- Looks up the unique index for the type variable 'ident' in the type
-- variable table of the current scope.
getTVar :: Ident -> Gen CTVarIName
getTVar i = do
  mix <- S.gets $ Map.lookup i . topStack . tvarScope
  case mix of
    Nothing -> genTVar i
    Just tv -> return tv

mapWithReset :: (a -> Gen b) -> [a] -> Gen [b]
mapWithReset act xs = forM xs $ \ x -> act x >>= \y -> resetScope >> return y
  where
  -- Sets the index counter back to zero and deletes all stack entries.
  resetScope = S.modify $ \ s -> s
    { varIndex  = 0
    , tvarIndex = 0
    , varScope  = [Map.empty]
    , tvarScope = [Map.empty]
    }

inNestedScope :: Gen a -> Gen a
inNestedScope act = beginScope >> act >>= \res -> endScope >> return res
  where
  -- Starts a new scope, i.e., copies and pushes the variable table
  -- of the current scope onto the top of the stack.
  beginScope = S.modify $ \s -> s
    { varScope = dupStack (varScope s), tvarScope = dupStack (tvarScope s) }

  -- End the current scope, i.e., pops and deletes the variable table
  -- of the current scope from the top of the stack.
  endScope = S.modify $ \s -> s
    { varScope = popStack (varScope s), tvarScope = popStack (tvarScope s) }

mapStack :: (a -> a) -> [a] -> [a]
mapStack _ []       = error "Gen.GenAbstractCurry.mapStack: empty stack"
mapStack f (x : xs) = f x : xs

topStack :: [a] -> a
topStack []      = error "Gen.GenAbstractCurry.topStack: empty stack"
topStack (x : _) = x

dupStack :: [a] -> [a]
dupStack []       = error "Gen.GenAbstractCurry.dupStack: empty stack"
dupStack (x : xs) = x : x : xs

popStack :: [a] -> [a]
popStack []       = error "Gen.GenAbstractCurry.popStack: empty stack"
popStack [x]      = [x]
popStack (_ : xs) = xs

-- ---------------------------------------------------------------------------
-- Partition of declarations
-- ---------------------------------------------------------------------------

-- The following code is used to split a list of Curry declarations into
-- three groups:
--   * a list of type declarations (data types and type synonyms),
--   * a table of function declarations,
--   * a list of fixity declarations for infix operators.

-- |Partition of Curry declarations.
-- (according to the definition of the AbstractCurry program
-- representation; type 'CurryProg').
-- Since a complete function declaration usually consists of more than one
-- declaration (e.g. rules, type signature etc.), it is necessary
-- to collect them within an association list
data Partition = Partition
  { typeDecls :: [Decl]
  , funcDecls :: [(Ident, [Decl])] -- no use of Map to preserve order
  , opDecls   :: [Decl]
  , patDecls  :: [Decl]
  , freeDecls :: [Decl]
  } deriving Show

partitionDecls :: [Decl] -> Partition
partitionDecls = rev . foldl part (Partition [] [] [] [] [])
  where
  -- operator infix declarations
  part p d@(InfixDecl      _ _ _ _) = p { opDecls   = d : opDecls   p }
  -- type declarations
  part p d@(DataDecl       _ _ _ _) = p { typeDecls = d : typeDecls p }
  part p d@(NewtypeDecl    _ _ _ _) = p { typeDecls = d : typeDecls p }
  part p d@(TypeDecl       _ _ _ _) = p { typeDecls = d : typeDecls p }
  -- function declarations
  part p (TypeSig       pos ids ty) = addFuncs p
                                    $ map (\f -> (f, TypeSig pos [f] ty)) ids
  part p d@(FunctionDecl     _ f _) = addFuncs p [(f, d)]
  part p d@(ForeignDecl  _ _ _ f _) = addFuncs p [(f, d)]
  part p (ExternalDecl     pos ids) = addFuncs p
                                    $ map (\f -> (f, ExternalDecl pos [f])) ids
  -- pattern declarations
  part p d@(PatternDecl      _ _ _) = p { patDecls  = d : patDecls  p }
  -- free variable declarations
  part p d@(FreeDecl           _ _) = p { freeDecls = d : freeDecls p }

  addFuncs p ds = p { funcDecls = foldl (flip insert) (funcDecls p) ds }
    where
    insert (f, d) []              = [(f, [d])]
    insert (f, d) ((g, gds) : ods)
      | f == g    = (g, d : gds) : ods
      | otherwise = (g,     gds) : insert (f, d) ods

  rev (Partition ts fs os ps vs) = Partition (reverse ts) fs (reverse os)
                                             (reverse ps)    (reverse vs)

-- -----------------------------------------------------------------------------
-- Conversion from Curry to AbstractCurry
-- -----------------------------------------------------------------------------

genModule :: Module -> Gen CurryProg
genModule (Module _ mid _ is ds) = do
  ts <- mapWithReset genTypeDecl       $ typeDecls part
  fs <- mapWithReset genPublicFuncDecl $ funcDecls part
  os <- concatMapM   genOpDecl         $ opDecls   part
  return $ CurryProg (moduleName mid) (map genImportDecl is) ts fs os
  where part = partitionDecls ds

genImportDecl :: ImportDecl -> String
genImportDecl (ImportDecl _ mid _ _ _) = moduleName mid

genTypeDecl :: Decl -> Gen CTypeDecl
genTypeDecl (DataDecl    _ n vs cs) = liftM4 CType    (genPublicTypeName n)
  (genVisibility n) (mapM genTVar vs) (mapM genConsDecl cs)
genTypeDecl (NewtypeDecl _ n vs nc) = liftM4 CType    (genPublicTypeName n)
  (genVisibility n) (mapM genTVar vs) (mapM genNConsDecl [nc])
genTypeDecl (TypeDecl    _ n vs ty) = liftM4 CTypeSyn (genPublicTypeName n)
  (genVisibility n) (mapM genTVar vs) (genTypeExpr ty)
genTypeDecl _
  = internalError "GenAbstractCurry.genTypeDecl: Unexpected declaration"

genConsDecl :: ConstrDecl -> Gen CConsDecl
genConsDecl (ConstrDecl _ _ n vs) = do
  qid <- genPublicFuncName n
  vis <- genVisibility n
  vs' <- mapM genTypeExpr vs
  return (CCons qid (length vs) vis vs')
genConsDecl (ConOpDecl p vs ty1 op ty2)
  = genConsDecl (ConstrDecl p vs op [ty1, ty2])

genNConsDecl :: NewConstrDecl -> Gen CConsDecl
genNConsDecl (NewConstrDecl p vs nc ty) = genConsDecl (ConstrDecl p vs nc [ty])

genTypeExpr :: TypeExpr -> Gen CTypeExpr
genTypeExpr (ConstructorType q vs) = liftM2 CTCons (genTypeName q)
                                     (mapM genTypeExpr vs)
genTypeExpr (VariableType      tv) = CTVar `liftM` getTVar tv
genTypeExpr (TupleType         ts) = genTypeExpr $ tuple2Cons ConstructorType ts
genTypeExpr (ListType          ty) = genTypeExpr $ ConstructorType qListId [ty]
genTypeExpr (ArrowType    ty1 ty2) = liftM2 CFuncType
                                     (genTypeExpr ty1) (genTypeExpr ty2)
genTypeExpr (RecordType    fss mr) = do
  let (fs, mty) = unchainRecords fss mr
      (ls, tys) = unzip fs
  tys' <- mapM genTypeExpr tys
  mty' <- mapM getTVar     mty
  return (CRecordType (zip (map conIdent ls) tys') mty')

-- | Unchain record updates, i.e., transform
--   @{ l1 :: a | l2 :: b | l1 :: c | d }@
--  to @{ l1 :: a, l2 :: b | d}@.
unchainRecords :: [([Ident], TypeExpr)] -> Maybe TypeExpr
               -> ([(Ident, TypeExpr)], Maybe Ident)
unchainRecords fss0 mty0 = unchain (flatFields fss0) mty0
  where
  unchain fs Nothing                     = (fs, Nothing)
  unchain fs (Just (VariableType    tv)) = (fs, Just tv)
  unchain fs (Just (RecordType fss mty)) = (foldr insertField fs' fs, mty')
    where (fs', mty') = unchainRecords fss mty
  unchain _  (Just                   ty) = internalError $
    "GenAbstractCurry.unchainRecords: Illegal record base `" ++ show ty ++ "'"

  flatFields fss = concatMap (\ (ls, ty) -> map (\l -> (l, ty)) ls) fss

  insertField kv        []             = [kv]
  insertField kv@(k, v) ((l, w) : kvs)
    | k == l    = (k, v) : kvs
    | otherwise = (l, w) : insertField kv kvs

genOpDecl :: Decl -> Gen [COpDecl]
genOpDecl (InfixDecl _ fix prec ops) = mapM genCOp ops
  where genCOp op = do
          op' <- genPublicFuncName op
          return $ COp op' (conFixity fix) (fromInteger prec)
genOpDecl _ = internalError "GenAbstractCurry.genOpDecl: No infix declaration"

conFixity :: Infix -> CFixity
conFixity InfixL = CInfixlOp
conFixity InfixR = CInfixrOp
conFixity Infix  = CInfixOp

genPublicFuncDecl :: (Ident, [Decl]) -> Gen CFuncDecl
genPublicFuncDecl (f, ds) = do
  mid <- getModuleIdent
  genFuncDecl (qualifyWith mid f, ds)

genLocalFuncDecl :: (Ident, [Decl]) -> Gen CFuncDecl
genLocalFuncDecl (f, ds) = genFuncDecl (qualify f, ds)

-- Generate an AbstractCurry function declaration
-- from a list of CurrySyntax function declarations.
-- NOTES:
--   - every declaration in 'ds' must declare exactly one function.
--   - since inferred types are internally represented in flat style,
--     all type variables are renamed with generated symbols when
--     generating typed AbstractCurry.
genFuncDecl :: (QualIdent, [Decl]) -> Gen CFuncDecl
genFuncDecl (f, ds) = do
  typed <- getAcyType
  f'    <- genFuncName   f
  vis   <- genVisibility (unqualify f)
  mty   <- case typed of
    UntypedAcy -> mapM genTypeSig (find isTypeSig ds)
    TypedAcy   -> qualLookupType f >>= mapM genTypeExpr
  rls   <- case find isFunctionDecl ds of
    Just (FunctionDecl _ _ eqs) -> mapM genRule eqs
    _                           -> return []
  let arity     = compArity mty rls
      typeexpr  = fromMaybe (CTCons ("Prelude", "untyped") []) mty
  return (CFunc f' arity vis typeexpr rls)
  where

  genTypeSig (TypeSig         _ _ ts) = genTypeExpr ts
  genTypeSig (ForeignDecl _ _ _ _ ts) = genTypeExpr ts
  genTypeSig _ =
    internalError "GenAbstractCurry.genFuncDecl.genTypeSig: No type signature"

  compArity _         (CRule ps _ : _) = length ps
  compArity (Just ty) []               = typeArity ty
  compArity Nothing   []               = internalError $
    "GenAbstractCurry.compArity: unable to compute arity for function `"
        ++ show f ++ "'"

  typeArity (CFuncType  _ t2) = 1 + typeArity t2
  typeArity _                 = 0

genRule :: Equation -> Gen CRule
genRule (Equation _ lhs rhs) = inNestedScope $
  liftM2 CRule (mapM genPat $ snd $ flatLhs lhs) (genRhs rhs)

genRhs :: Rhs -> Gen CRhs
genRhs (SimpleRhs  _ e ds) = liftM2 (flip  CSimpleRhs) (genLocalDecls ds)
                             (genExpr e)
genRhs (GuardedRhs  cs ds) = liftM2 (flip CGuardedRhs) (genLocalDecls ds)
                             (mapM genCondExpr cs)

genCondExpr :: CondExpr -> Gen (CExpr, CExpr)
genCondExpr (CondExpr _ c e) = liftM2 (,) (genExpr c) (genExpr e)

genLocalDecls :: [Decl] -> Gen [CLocalDecl]
genLocalDecls ds = do
  funs <- mapM       (inNestedScope . genLFuncDecl) (funcDecls part)
  pats <- mapM       (inNestedScope . genLPattern ) (patDecls  part)
  vars <- concatMapM (inNestedScope . genLFreeDecl) (freeDecls part)
  return $ concat [funs, pats, vars]
  where
  part = partitionDecls ds

  genLFuncDecl = liftM CLocalFunc . genLocalFuncDecl

  genLPattern (PatternDecl   _ p rhs) = liftM2 CLocalPat (genPat p) (genRhs rhs)
  genLPattern _
    = internalError "GenAbstractCurry.genLocalDecls.genLPattern"

  genLFreeDecl (FreeDecl        _ vs) = mapM genVar' vs
    where genVar' v = CLocalVar `liftM` genVar v
  genLFreeDecl _
    = internalError "GenAbstractCurry.genLocalDecls.genLFreeDecl"

genExpr :: Expression -> Gen CExpr
genExpr (Literal               l) = return $ CLit $ conLiteral l
genExpr (Variable              v) = do
  midx <- lookupVar (unqualify v)
  case midx of
    Just v'                   -> return $ CVar v'
    Nothing | v == qSuccessId -> CSymbol `liftM` genFuncName qSuccessFunId
            | otherwise       -> CSymbol `liftM` genFuncName v
genExpr (Constructor           c) = CSymbol `liftM` genFuncName c
genExpr (Paren                 e) = genExpr e
genExpr (Typed               e _) = genExpr e
genExpr (Tuple              _ es) = genExpr $ tuple2Cons comb es
  where comb qid bs = apply (Variable qid) bs
genExpr (List               _ es)
  = let cons = Constructor qConsId
        nil  = Constructor qNilId
    in  genExpr (foldr (Apply . Apply cons) nil es)
genExpr (ListCompr        _ e ss) = inNestedScope $ liftM2 (flip CListComp)
                                    (mapM genStatement ss) (genExpr e)
genExpr (EnumFrom              e) = genExpr (Apply (Variable qEnumFromId) e)
genExpr (EnumFromThen      e1 e2)
  = genExpr (apply (Variable qEnumFromThenId) [e1, e2])
genExpr (EnumFromTo        e1 e2)
  = genExpr (apply (Variable qEnumFromToId) [e1, e2])
genExpr (EnumFromThenTo e1 e2 e3)
  = genExpr (apply (Variable qEnumFromThenToId) [e1, e2, e3])
genExpr (UnaryMinus          _ e) = genExpr (Apply (Variable qNegateId) e)
genExpr (Apply             e1 e2) = liftM2 CApply (genExpr e1) (genExpr e2)
genExpr (InfixApply     e1 op e2) = genExpr (apply (infixOp op) [e1, e2])
genExpr (LeftSection        e op) = genExpr $ Apply (infixOp op) e
genExpr (RightSection       op e) = genExpr $ apply (Variable qFlipId)
                                    [infixOp op, e]
genExpr (Lambda           _ ps e) = inNestedScope $
  liftM2 CLambda (mapM genPat ps) (genExpr e)
genExpr (Let                ds e) = inNestedScope $
  liftM2 CLetDecl (genLocalDecls ds) (genExpr e)
genExpr (Do                 ss e) = inNestedScope $ do
  ss' <- mapM genStatement ss
  e'  <- genExpr e
  return $ CDoExpr (ss' ++ [CSExpr e'])
genExpr (IfThenElse   _ e1 e2 e3)
  = genExpr (apply (Variable qIfThenElseId) [e1, e2, e3])
genExpr (Case          _ ct e bs)
  = liftM2 (CCase $ conCaseType ct) (genExpr e) (mapM genBranchExpr bs)
genExpr (RecordConstr         fs)
  = CRecConstr `liftM` mapM (genField genExpr) fs
genExpr (RecordSelection     e l) = do
  e' <- genExpr e
  return (CRecSelect e' $ conIdent l)
genExpr (RecordUpdate       fs e)
  = liftM2 CRecUpdate (mapM (genField genExpr) fs) (genExpr e)

conCaseType :: CaseType -> CCaseType
conCaseType Flex  = CFlex
conCaseType Rigid = CRigid

genStatement :: Statement -> Gen CStatement
genStatement (StmtExpr   _ e) = CSExpr `liftM` genExpr e
genStatement (StmtDecl    ds) = CSLet  `liftM` genLocalDecls ds
genStatement (StmtBind _ p e) = liftM2 (flip CSPat) (genExpr e) (genPat p)

genBranchExpr :: Alt -> Gen (CPattern, CRhs)
genBranchExpr (Alt _ pat rhs) = inNestedScope $ do
  pat' <- genPat pat
  rhs' <- genRhs rhs
  return (pat', rhs')

genPat ::Pattern -> Gen CPattern
genPat (LiteralPattern         l) = return $ CPLit $ conLiteral l
genPat (VariablePattern        v) = CPVar `liftM` genVar v
genPat (ConstructorPattern  c ps)
  = liftM2 CPComb (genFuncName c) (mapM genPat ps)
genPat (InfixPattern     p1 c p2) = genPat $ ConstructorPattern c [p1, p2]
genPat (ParenPattern           p) = genPat p
genPat (TuplePattern        _ ps) = genPat $ tuple2Cons ConstructorPattern ps
genPat (ListPattern         _ ps) = genPat $
  foldr (\x1 x2 -> ConstructorPattern qConsId [x1, x2])
        (ConstructorPattern qNilId []) ps
genPat (NegativePattern      _ l) = genPat $ LiteralPattern $ negateLiteral l
genPat (AsPattern            v p) = liftM2 (flip CPAs) (genPat p) (genVar v)
genPat (LazyPattern          _ p) = CPLazy `liftM` genPat p
genPat (FunctionPattern     f ps) = liftM2 CPFuncComb (genFuncName f)
                                    (mapM genPat ps)
genPat (InfixFuncPattern p1 f p2) = genPat (FunctionPattern f [p1, p2])
genPat (RecordPattern      fs mr) = liftM2 CPRecord (mapM (genField genPat) fs)
                                    (mapM genPat mr)

genField :: (a -> Gen b) -> Field a -> Gen (CField b)
genField genTerm (Field _ l t) = (\t' -> (conIdent l, t')) `liftM` genTerm t

-- |Convert an identifier.
conIdent :: Ident -> String
conIdent = idName

negateLiteral :: Literal -> Literal
negateLiteral (Int   x i) = Int   x (-i)
negateLiteral (Float r f) = Float r (-f)
negateLiteral l           = internalError $
  "GenAbstractCurry.negateLiteral: " ++ show l

conLiteral :: Literal -> CLiteral
conLiteral (Char   _ c) = CCharc  c
conLiteral (Int    _ i) = CIntc   i
conLiteral (Float  _ f) = CFloatc f
conLiteral (String _ s) = CString s

genPublicTypeName :: Ident -> Gen QName
genPublicTypeName i = do
  mid <- getModuleIdent
  genTypeName (qualifyWith mid i)

genPublicFuncName :: Ident -> Gen QName
genPublicFuncName i = do
  mid <- getModuleIdent
  genFuncName (qualifyWith mid i)

genTypeName :: QualIdent -> Gen QName
genTypeName = genQName True

genFuncName :: QualIdent -> Gen QName
genFuncName = genQName False

-- |Create a qualified AbstractCurry identifier from a Curry 'QualIdent'.
--
-- * Some prelude identifiers are not qualified. The first check ensures
--   that they get a correct qualifier.
-- * The test for unqualified identifiers is necessary to qualify
--   them correctly in the untyped AbstractCurry representation.
genQName :: Bool -> QualIdent -> Gen QName
genQName isTypeCons qid
  | isPreludeIdent qid = genQualName $ qualQualify preludeMIdent qid
  | isQualified    qid = genQualName qid
  | otherwise          = getQualIdent >>= genQualName
  where
  getQualIdent | isTypeCons = lookupTypeName  qid
               | otherwise  = lookupValueName qid

  genQualName qid' = do
    mid <- getModuleIdent
    return ( moduleName $ fromMaybe mid $ qidModule qid'
           , conIdent   $                 qidIdent  qid'
           )

-- Checks, whether a symbol is defined in the Prelude.
isPreludeIdent :: QualIdent -> Bool
isPreludeIdent qid = qidModule qid == Just preludeMIdent
                  || ident `elem` [unitId, listId, nilId, consId]
                  || isTupleId ident
                  where ident = qidIdent qid

genVisibility :: Ident -> Gen CVisibility
genVisibility i = isExported i >>= \b -> return $ if b then Public else Private

tuple2Cons :: (QualIdent -> [a] -> a) -> [a] -> a
tuple2Cons f []  = f qUnitId []
tuple2Cons _ [x] = x
tuple2Cons f xs  = f (qTupleId $ length xs) xs

apply :: Expression -> [Expression] -> Expression
apply = foldl Apply

-- -----------------------------------------------------------------------------
-- Prelude identifiers
-- -----------------------------------------------------------------------------

qEnumFromId :: QualIdent
qEnumFromId = qualifyWith preludeMIdent (mkIdent "enumFrom")

qEnumFromThenId :: QualIdent
qEnumFromThenId = qualifyWith preludeMIdent (mkIdent "enumFromThen")

qEnumFromToId :: QualIdent
qEnumFromToId = qualifyWith preludeMIdent (mkIdent "enumFromTo")

qEnumFromThenToId :: QualIdent
qEnumFromThenToId = qualifyWith preludeMIdent (mkIdent "enumFromThenTo")

qNegateId :: QualIdent
qNegateId = qualifyWith preludeMIdent (mkIdent "negate")

qIfThenElseId :: QualIdent
qIfThenElseId = qualifyWith preludeMIdent (mkIdent "if_then_else")

qSuccessFunId :: QualIdent
qSuccessFunId = qualifyWith preludeMIdent (mkIdent "success")

qFlipId :: QualIdent
qFlipId = qualifyWith preludeMIdent (mkIdent "flip")
