{- |
    Module      :  $Header$
    Description :  Generation of AbstractCurry program terms
    Copyright   :  (c) 2005        Martin Engelke
                       2011 - 2015 Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of an 'AbstractCurry' program term
    for a given 'Curry' module.
-}
{-# LANGUAGE CPP #-}
module Generators.GenAbstractCurry (genAbstractCurry) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative          ((<$>), (<*>), pure)
#endif
import           Control.Monad.Extra
import qualified Control.Monad.State as S     (State, evalState, get, gets
                                              , modify, put, when)
import qualified Data.Map            as Map   (Map, empty, fromList, lookup
                                              , union)
import qualified Data.Maybe          as Maybe (fromJust, fromMaybe, listToMaybe)
import qualified Data.Set            as Set   (Set, empty, insert, member)
import qualified Data.Traversable    as T     (forM)

import Curry.AbstractCurry
import Curry.Base.Ident
import Curry.Syntax

import Base.CurryTypes (fromPredType, toType, toPredType)
import Base.Expr       (bv)
import Base.Messages   (internalError)
import Base.NestEnv
import Base.Types      (TypeScheme (..))
import Base.TypeSubst

import Env.Value       (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)
import Env.OpPrec      (mkPrec)

import CompilerEnv

type GAC a = S.State AbstractEnv a

-- ---------------------------------------------------------------------------
-- Interface
-- ---------------------------------------------------------------------------

-- |Generate an AbstractCurry program term from the syntax tree
--  when uacy flag is set untype AbstractCurry is generated
genAbstractCurry :: Bool -> CompilerEnv -> Module a -> CurryProg
genAbstractCurry uacy env mdl
  = S.evalState (trModule $ fmap (const ()) mdl) (abstractEnv uacy env mdl)

-- ---------------------------------------------------------------------------
-- Conversion from Curry to AbstractCurry
-- ---------------------------------------------------------------------------

trModule :: Module () -> GAC CurryProg
trModule (Module _ mid _ is ds) = do
  CurryProg mid' is' <$> dflt' <*> cds' <*> ids' <*> ts' <*> fs' <*> os'
  where
  mid'  = moduleName mid
  is'   = map cvImportDecl is
  dflt' = Maybe.listToMaybe <$> concatMapM (withLocalEnv . trDefaultDecl) ds
  cds'  = concatMapM (withLocalEnv . trClassDecl) ds
  ids'  = concatMapM (withLocalEnv . trInstanceDecl) ds
  ts'   = concatMapM (withLocalEnv . trTypeDecl) ds
  fs'   = concatMapM (withLocalEnv . trFuncDecl True) ds
  os'   = concatMapM (withLocalEnv . trInfixDecl) ds

cvImportDecl :: ImportDecl -> String
cvImportDecl (ImportDecl _ mid _ _ _) = moduleName mid

trDefaultDecl :: Decl a -> GAC [CDefaultDecl]
trDefaultDecl (DefaultDecl _ tys) = (\tys' -> [CDefaultDecl tys'])
  <$> mapM trTypeExpr tys
trDefaultDecl _                   = return []

trClassDecl :: Decl () -> GAC [CClassDecl]
trClassDecl (ClassDecl _ cx cls tv ds) = do
  (\cls' v' cx' tv' ds' -> [CClass cls' v' cx' tv' ds'])
    <$> trGlobalIdent cls <*> getTypeVisibility cls <*> trContext cx
    <*> getTVarIndex tv <*> concatMapM (trClassMethodDecl sigs fs) ds
  where fs = [f | FunctionDecl _ _ f _ <- ds]
        sigs = signatures ds
trClassDecl _ = return []

-- We ignore type signatures for class methods with a given default
-- implementation as declarations for those are generated anyway.
-- For function declarations we use the equation's arity instead of
-- the one from the value environment or 0.
trClassMethodDecl :: [(Ident, QualTypeExpr)] -> [Ident] -> Decl ()
                  -> GAC [CFuncDecl]
trClassMethodDecl sigs fs (TypeSig p [f] _) | f `notElem` fs =
  trClassMethodDecl sigs fs $ FunctionDecl p () f []
trClassMethodDecl sigs fs (TypeSig p (f:f':fs') qty) = do
  liftM2 (++) (trClassMethodDecl sigs fs $ TypeSig p [f] qty)
              (trClassMethodDecl sigs fs $ TypeSig p (f':fs') qty)
trClassMethodDecl sigs _ (FunctionDecl _ _ f eqs) =
  (\f' a v ty rs -> [CFunc f' a v ty rs]) <$> trGlobalIdent f
  <*> pure (maybe 0 eqnArity $ Maybe.listToMaybe eqs)
  <*> getVisibility (unRenameIdent f)
  <*> trQualTypeExpr (Maybe.fromJust $ lookup f sigs) <*> mapM trEquation eqs
trClassMethodDecl _ _ _ = return []

trInstanceDecl :: Decl () -> GAC [CInstanceDecl]
trInstanceDecl (InstanceDecl _ cx qcls ty ds) =
  (\qcls' cx' ty' ds' -> [CInstance qcls' cx' ty' ds']) <$> trQual qcls
  <*> trContext cx <*> trTypeExpr ty <*> mapM (trInstanceMethodDecl qcls ty) ds
trInstanceDecl _ = return []

-- Again, we use the equation's arity for function declarations instead of
-- the one from the value.
trInstanceMethodDecl :: QualIdent -> TypeExpr -> Decl () -> GAC CFuncDecl
trInstanceMethodDecl qcls ty (FunctionDecl _ _ f eqs) = do
  uacy <- S.gets untypedAcy
  qty <- if uacy
           then return $ QualTypeExpr [] $ ConstructorType prelUntyped
           else getQualType' (qualifyLike qcls $ unRenameIdent f) uacy
  CFunc <$> trLocalIdent f <*> pure (eqnArity $ head eqs) <*> pure Public
        <*> trInstanceMethodType ty qty <*> mapM trEquation eqs
trInstanceMethodDecl _ _ _ = internalError "GenAbstractCurry.trInstanceMethodDecl"

-- Transforms a class method type into an instance method's type by replacing
-- the class variable with the given instance type. The implicit class context
-- is dropped in doing so.
trInstanceMethodType :: TypeExpr -> QualTypeExpr -> GAC CQualTypeExpr
trInstanceMethodType ity (QualTypeExpr cx ty) =
  trQualTypeExpr $ fromPredType identSupply $
    subst (bindSubst 0 (toType [] ity) idSubst) $
      toPredType (take 1 identSupply) $ QualTypeExpr (drop 1 cx) ty

trTypeDecl :: Decl a -> GAC [CTypeDecl]
trTypeDecl (DataDecl    _ t vs cs) = (\t' v vs' cs' -> [CType t' v vs' cs'])
  <$> trGlobalIdent t <*> getTypeVisibility t
  <*> mapM genTVarIndex vs <*> mapM trConsDecl cs
trTypeDecl (TypeDecl    _ t vs ty) = (\t' v vs' ty' -> [CTypeSyn t' v vs' ty'])
  <$> trGlobalIdent t <*> getTypeVisibility t
  <*> mapM genTVarIndex vs <*> trTypeExpr ty
trTypeDecl (NewtypeDecl _ t vs nc) = (\t' v vs' nc' -> [CNewType t' v vs' nc'])
  <$> trGlobalIdent t <*> getTypeVisibility t
  <*> mapM genTVarIndex vs <*> trNewConsDecl nc
trTypeDecl _                       = return []

trConsDecl :: ConstrDecl -> GAC CConsDecl
trConsDecl (ConstrDecl  _ vs cx c tys) = inNestedTScope $ CCons
  <$> mapM genTVarIndex vs <*> trContext cx <*> trGlobalIdent c
  <*> getVisibility c <*> mapM trTypeExpr tys
trConsDecl (ConOpDecl p vs cx ty1 op ty2) = inNestedTScope $ trConsDecl $
  ConstrDecl p vs cx op [ty1, ty2]
trConsDecl (RecordDecl   _ vs cx c fs) = inNestedTScope $ CRecord
  <$> mapM genTVarIndex vs <*> trContext cx <*> trGlobalIdent c
  <*> getVisibility c <*> concatMapM trFieldDecl fs

trFieldDecl :: FieldDecl -> GAC [CFieldDecl]
trFieldDecl (FieldDecl _ ls ty) = T.forM ls $ \l ->
  CField <$> trGlobalIdent l <*> getVisibility l <*> trTypeExpr ty

trNewConsDecl :: NewConstrDecl -> GAC CConsDecl
trNewConsDecl (NewConstrDecl _ nc      ty) = CCons [] (CContext [])
  <$> trGlobalIdent nc <*> getVisibility nc <*> ((:[]) <$> trTypeExpr ty)
trNewConsDecl (NewRecordDecl p nc (l, ty)) = CRecord [] (CContext [])
  <$> trGlobalIdent nc <*> getVisibility nc <*> trFieldDecl (FieldDecl p [l] ty)

trTypeExpr :: TypeExpr -> GAC CTypeExpr
trTypeExpr (ConstructorType q) = CTCons <$> trQual q
trTypeExpr (ApplyType ty1 ty2) = CTApply <$> trTypeExpr ty1 <*> trTypeExpr ty2
trTypeExpr (VariableType    v) = CTVar  <$> getTVarIndex v
trTypeExpr (TupleType     tys) =
  trTypeExpr $ foldr ApplyType (ConstructorType $ qTupleId $ length tys) tys
trTypeExpr (ListType       ty) =
  trTypeExpr $ ApplyType (ConstructorType qListId) ty
trTypeExpr (ArrowType ty1 ty2) = CFuncType <$> trTypeExpr ty1 <*> trTypeExpr ty2
trTypeExpr (ParenType      ty) = trTypeExpr ty

trConstraint :: Constraint -> GAC CConstraint
trConstraint (Constraint q ty) = (,) <$> trQual q <*> trTypeExpr ty

trContext :: Context -> GAC CContext
trContext cx = CContext <$> mapM trConstraint cx

trQualTypeExpr :: QualTypeExpr -> GAC CQualTypeExpr
trQualTypeExpr (QualTypeExpr cx ty) =
  CQualType <$> trContext cx <*> trTypeExpr ty

trInfixDecl :: Decl a -> GAC [COpDecl]
trInfixDecl (InfixDecl _ fix mprec ops) = mapM trInfix (reverse ops)
  where
  trInfix op = COp <$> trGlobalIdent op <*> return (cvFixity fix)
                   <*> return (fromInteger (mkPrec mprec))
  cvFixity InfixL = CInfixlOp
  cvFixity InfixR = CInfixrOp
  cvFixity Infix  = CInfixOp
trInfixDecl _ = return []

trFuncDecl :: Bool -> Decl () -> GAC [CFuncDecl]
trFuncDecl global (FunctionDecl  _ _ f eqs)
  =   (\f' a v ty rs -> [CFunc f' a v ty rs])
  <$> trFuncName global f <*> getArity f <*> getVisibility f
  <*> getQualType f <*> mapM trEquation eqs
trFuncDecl global (ForeignDecl _ _ _ _ f _)
  =   (\f' a v ty rs -> [CFunc f' a v ty rs])
  <$> trFuncName global f <*> getArity f <*> getVisibility f
  <*> getQualType f <*> return []
trFuncDecl global (ExternalDecl       _ vs)
  =   T.forM (map varIdent vs) $ \f -> CFunc
  <$> trFuncName global f <*> getArity f <*> getVisibility f
  <*> getQualType f <*> return []
trFuncDecl _      _                           = return []

trFuncName :: Bool -> Ident -> GAC QName
trFuncName global = if global then trGlobalIdent else trLocalIdent

trEquation :: Equation () -> GAC CRule
trEquation (Equation _ lhs rhs) = inNestedScope
                                $ CRule <$> trLhs lhs <*> trRhs rhs

trLhs :: Lhs () -> GAC [CPattern]
trLhs = mapM trPat . snd . flatLhs

trRhs :: Rhs () -> GAC CRhs
trRhs (SimpleRhs _ e ds) = inNestedScope $ do
  mapM_ insertDeclLhs ds
  CSimpleRhs <$> trExpr e <*> concatMapM trLocalDecl ds
trRhs (GuardedRhs gs ds) = inNestedScope $ do
  mapM_ insertDeclLhs ds
  CGuardedRhs <$> mapM trCondExpr gs <*> concatMapM trLocalDecl ds

trCondExpr :: CondExpr () -> GAC (CExpr, CExpr)
trCondExpr (CondExpr _ g e) = (,) <$> trExpr g <*> trExpr e

trLocalDecls :: [Decl ()] -> GAC [CLocalDecl]
trLocalDecls ds = do
  mapM_ insertDeclLhs ds
  concatMapM trLocalDecl ds

-- Insert all variables declared in local declarations
insertDeclLhs :: Decl a -> GAC ()
insertDeclLhs   (PatternDecl      _ p _) = mapM_ genVarIndex (bv p)
insertDeclLhs   (FreeDecl          _ vs) = mapM_ genVarIndex (map varIdent vs)
insertDeclLhs s@(TypeSig          _ _ _) = do
  uacy <- S.gets untypedAcy
  S.when uacy (insertSig s)
insertDeclLhs _                          = return ()

trLocalDecl :: Decl () -> GAC [CLocalDecl]
trLocalDecl f@(FunctionDecl    _ _ _ _) = map CLocalFunc <$> trFuncDecl False f
trLocalDecl f@(ForeignDecl _ _ _ _ _ _) = map CLocalFunc <$> trFuncDecl False f
trLocalDecl f@(ExternalDecl        _ _) = map CLocalFunc <$> trFuncDecl False f
trLocalDecl (PatternDecl       _ p rhs) = (\p' rhs' -> [CLocalPat p' rhs'])
                                          <$> trPat p <*> trRhs rhs
trLocalDecl (FreeDecl             _ vs) = (\vs' -> [CLocalVars vs'])
                                          <$> mapM getVarIndex (map varIdent vs)
trLocalDecl _                           = return [] -- can not occur (types etc.)

insertSig :: Decl a -> GAC ()
insertSig (TypeSig _ fs qty) = do
  sigs <- S.gets typeSigs
  let lsigs = Map.fromList [(f, qty) | f <- fs]
  S.modify $ \env -> env { typeSigs = sigs `Map.union` lsigs }
insertSig _                 = return ()

trExpr :: Expression () -> GAC CExpr
trExpr (Literal       _ l) = return (CLit $ cvLiteral l)
trExpr (Variable      _ v)
  | isQualified v = CSymbol <$> trQual v
  | otherwise     = lookupVarIndex (unqualify v) >>= \mvi -> case mvi of
    Just vi -> return (CVar vi)
    _       -> CSymbol <$> trQual v
trExpr (Constructor   _ c) = CSymbol <$> trQual c
trExpr (Paren           e) = trExpr e
trExpr (Typed       e qty) = CTyped <$> trExpr e <*> trQualTypeExpr qty
trExpr (Record     _ c fs) = CRecConstr <$> trQual c
                                        <*> mapM (trField trExpr) fs
trExpr (RecordUpdate e fs) = CRecUpdate <$> trExpr e
                                        <*> mapM (trField trExpr) fs
trExpr (Tuple        _ es) =
  trExpr $ apply (Variable () $ qTupleId $ length es) es
trExpr (List       _ _ es) = trExpr $
  foldr (Apply . Apply (Constructor () qConsId)) (Constructor () qNilId) es
trExpr (ListCompr  _ e ds) = inNestedScope $ flip CListComp
                             <$> mapM trStatement ds <*> trExpr e
trExpr (EnumFrom              e) =
  trExpr $ apply (Variable () qEnumFromId) [e]
trExpr (EnumFromThen      e1 e2) =
  trExpr $ apply (Variable () qEnumFromThenId) [e1, e2]
trExpr (EnumFromTo        e1 e2) =
  trExpr $ apply (Variable ()qEnumFromToId) [e1, e2]
trExpr (EnumFromThenTo e1 e2 e3) =
  trExpr $ apply (Variable () qEnumFromThenToId) [e1, e2, e3]
trExpr (UnaryMinus          _ e) = trExpr $ apply (Variable () qNegateId) [e]
trExpr (Apply             e1 e2) = CApply <$> trExpr e1 <*> trExpr e2
trExpr (InfixApply     e1 op e2) = trExpr $ apply (infixOp op) [e1, e2]
trExpr (LeftSection        e op) = trExpr $ apply (infixOp op) [e]
trExpr (RightSection       op e) = trExpr
                                 $ apply (Variable () qFlip) [infixOp op, e]
trExpr (Lambda           _ ps e) = inNestedScope $
                                   CLambda <$> mapM trPat ps <*> trExpr e
trExpr (Let                ds e) = inNestedScope $
                                   CLetDecl <$> trLocalDecls ds <*> trExpr e
trExpr (Do                 ss e) = inNestedScope $
                                   (\ss' e' -> CDoExpr (ss' ++ [CSExpr e']))
                                   <$> mapM trStatement ss <*> trExpr e
trExpr (IfThenElse   _ e1 e2 e3) =
  trExpr $ apply (Variable () qIfThenElseId) [e1, e2, e3]
trExpr (Case          _ ct e bs) = CCase (cvCaseType ct)
                                   <$> trExpr e <*> mapM trAlt bs

cvCaseType :: CaseType -> CCaseType
cvCaseType Flex  = CFlex
cvCaseType Rigid = CRigid

trStatement :: Statement () -> GAC CStatement
trStatement (StmtExpr   _ e) = CSExpr     <$> trExpr e
trStatement (StmtDecl    ds) = CSLet      <$> trLocalDecls ds
trStatement (StmtBind _ p e) = flip CSPat <$> trExpr e <*> trPat p

trAlt :: Alt () -> GAC (CPattern, CRhs)
trAlt (Alt _ p rhs) = inNestedScope $ (,) <$> trPat p <*> trRhs rhs

trPat :: Pattern () -> GAC CPattern
trPat (LiteralPattern         _ l) = return (CPLit $ cvLiteral l)
trPat (VariablePattern        _ v) = CPVar <$> getVarIndex v
trPat (ConstructorPattern  _ c ps) = CPComb <$> trQual c <*> mapM trPat ps
trPat (InfixPattern    a p1 op p2) = trPat $ ConstructorPattern a op [p1, p2]
trPat (ParenPattern             p) = trPat p
trPat (RecordPattern       _ c fs) = CPRecord <$> trQual c
                                              <*> mapM (trField trPat) fs
trPat (TuplePattern          _ ps) =
  trPat $ ConstructorPattern () (qTupleId $ length ps) ps
trPat (ListPattern         _ _ ps) = trPat $
  foldr (\x1 x2 -> ConstructorPattern () qConsId [x1, x2])
        (ConstructorPattern () qNilId [])
        ps
trPat (NegativePattern      a _ l) = trPat $ LiteralPattern a $ negateLiteral l
trPat (AsPattern              v p) = CPAs <$> getVarIndex v<*> trPat p
trPat (LazyPattern            _ p) = CPLazy <$> trPat p
trPat (FunctionPattern     _ f ps) = CPFuncComb <$> trQual f <*> mapM trPat ps
trPat (InfixFuncPattern a p1 f p2) = trPat (FunctionPattern a f [p1, p2])

trField :: (a -> GAC b) -> Field a -> GAC (CField b)
trField act (Field _ l x) = (,) <$> trQual l <*> act x

negateLiteral :: Literal -> Literal
negateLiteral (Int    v i) = Int   v  (-i)
negateLiteral (Float p' f) = Float p' (-f)
negateLiteral _            = internalError "GenAbstractCurry.negateLiteral"

cvLiteral :: Literal -> CLiteral
cvLiteral (Char   _ c) = CCharc   c
cvLiteral (Int    _ i) = CIntc    i
cvLiteral (Float  _ f) = CFloatc  f
cvLiteral (String _ s) = CStringc s

trQual :: QualIdent -> GAC QName
trQual qid
  | n `elem` [unitId, listId, nilId, consId] = return ("Prelude", idName n)
  | isTupleId n                              = return ("Prelude", idName n)
  | otherwise
  = return (maybe "" moduleName (qidModule qid), idName n)
  where n = qidIdent qid

trGlobalIdent :: Ident -> GAC QName
trGlobalIdent i = S.gets moduleId >>= \m -> return (moduleName m, idName i)

trLocalIdent :: Ident -> GAC QName
trLocalIdent i = return ("", idName i)

qFlip :: QualIdent
qFlip = qualifyWith preludeMIdent (mkIdent "flip")

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

prelUntyped :: QualIdent
prelUntyped = qualifyWith preludeMIdent $ mkIdent "untyped"

-------------------------------------------------------------------------------
-- This part defines an environment containing all necessary information
-- for generating the AbstractCurry representation of a CurrySyntax term.

-- |Data type for representing an AbstractCurry generator environment
data AbstractEnv = AbstractEnv
  { moduleId   :: ModuleIdent                -- ^name of the module
  , typeEnv    :: ValueEnv                   -- ^known values
  , tyExports  :: Set.Set Ident              -- ^exported type symbols
  , valExports :: Set.Set Ident              -- ^exported value symbols
  , varIndex   :: Int                        -- ^counter for variable indices
  , tvarIndex  :: Int                        -- ^counter for type variable indices
  , varEnv     :: NestEnv Int                -- ^stack of variable tables
  , tvarEnv    :: NestEnv Int                -- ^stack of type variable tables
  , untypedAcy :: Bool                       -- ^flag to indicate whether untyped
                                             --  AbstractCurry is generated
  , typeSigs   :: Map.Map Ident QualTypeExpr -- ^map of user defined type signatures
  } deriving Show

-- |Initialize the AbstractCurry generator environment
abstractEnv :: Bool -> CompilerEnv -> Module a -> AbstractEnv
abstractEnv uacy env (Module _ mid es _ ds) = AbstractEnv
  { moduleId   = mid
  , typeEnv    = valueEnv env
  , tyExports  = foldr (buildTypeExports  mid) Set.empty es'
  , valExports = foldr (buildValueExports mid) Set.empty es'
  , varIndex   = 0
  , tvarIndex  = 0
  , varEnv     = globalEnv emptyTopEnv
  , tvarEnv    = globalEnv emptyTopEnv
  , untypedAcy = uacy
  , typeSigs   = if uacy
                  then Map.fromList $ signatures ds
                  else Map.empty
  }
  where es' = case es of
          Just (Exporting _ e) -> e
          _                    -> internalError "GenAbstractCurry.abstractEnv"

-- Builds a table containing all exported identifiers from a module.
buildTypeExports :: ModuleIdent -> Export -> Set.Set Ident -> Set.Set Ident
buildTypeExports mid (ExportTypeWith tc _)
  | isLocalIdent mid tc = Set.insert (unqualify tc)
buildTypeExports _   _  = id

-- Builds a table containing all exported identifiers from a module.
buildValueExports :: ModuleIdent -> Export -> Set.Set Ident -> Set.Set Ident
buildValueExports mid (Export             q)
  | isLocalIdent mid q  = Set.insert (unqualify q)
buildValueExports mid (ExportTypeWith tc cs)
  | isLocalIdent mid tc = flip (foldr Set.insert) cs
buildValueExports _   _  = id

-- Looks up the unique index for the variable 'ident' in the
-- variable table of the current scope.
lookupVarIndex :: Ident -> GAC (Maybe CVarIName)
lookupVarIndex i = S.gets $ \env -> case lookupNestEnv i $ varEnv env of
  [v] -> Just (v, idName i)
  _   -> Nothing

getVarIndex :: Ident -> GAC CVarIName
getVarIndex i = S.get >>= \env -> case lookupNestEnv i $ varEnv env of
  [v] -> return (v, idName i)
  _   -> genVarIndex i

-- Generates an unique index for the  variable 'ident' and inserts it
-- into the  variable table of the current scope.
genVarIndex :: Ident -> GAC CVarIName
genVarIndex i = do
  env <- S.get
  let idx = varIndex env
  S.put $ env { varIndex = idx + 1, varEnv = bindNestEnv i idx (varEnv env) }
  return (idx, idName i)

-- Looks up the unique index for the type variable 'ident' in the type
-- variable table of the current scope.
getTVarIndex :: Ident -> GAC CTVarIName
getTVarIndex i = S.get >>= \env -> case lookupNestEnv i $ tvarEnv env of
  [v] -> return (v, idName i)
  _   -> genTVarIndex i

-- Generates an unique index for the type variable 'ident' and inserts it
-- into the type variable table of the current scope.
genTVarIndex :: Ident -> GAC CTVarIName
genTVarIndex i = do
  env <- S.get
  let idx = tvarIndex env
  S.put $ env { tvarIndex = idx + 1, tvarEnv = bindNestEnv i idx (tvarEnv env) }
  return (idx, idName i)

withLocalEnv :: GAC a -> GAC a
withLocalEnv act = do
  old <- S.get
  res <- act
  S.put old
  return res

inNestedScope :: GAC a -> GAC a
inNestedScope act = do
  (vo, to) <- S.gets $ \e -> (varEnv e, tvarEnv e)
  S.modify $ \e -> e { varEnv = nestEnv $ vo, tvarEnv = globalEnv emptyTopEnv }
  res <- act
  S.modify $ \e -> e { varEnv = vo, tvarEnv = to }
  return res

inNestedTScope :: GAC a -> GAC a
inNestedTScope act = do
  (vo, to) <- S.gets $ \e -> (varEnv e, tvarEnv e)
  S.modify $ \e -> e { varEnv = globalEnv emptyTopEnv, tvarEnv = nestEnv $ to }
  res <- act
  S.modify $ \e -> e { varEnv = vo, tvarEnv = to }
  return res

getArity :: Ident -> GAC Int
getArity f = do
  m     <- S.gets moduleId
  tyEnv <- S.gets typeEnv
  return $ case lookupValue f tyEnv of
    [Value _ _ a _] -> a
    _               -> case qualLookupValue (qualifyWith m f) tyEnv of
      [Value _ _ a _] -> a
      _               -> internalError $ "GenAbstractCurry.getArity: " ++ show f

getQualType :: Ident -> GAC CQualTypeExpr
getQualType f =
  S.gets untypedAcy >>= getQualType' (qualify f) >>= trQualTypeExpr

getQualType' :: QualIdent -> Bool -> GAC QualTypeExpr
getQualType' f True  = do
  sigs <- S.gets typeSigs
  return $ Maybe.fromMaybe (QualTypeExpr [] $ ConstructorType prelUntyped)
                           (Map.lookup (unqualify f) sigs)
getQualType' f False = do
  m     <- S.gets moduleId
  tyEnv <- S.gets typeEnv
  return $ case qualLookupValue f tyEnv of
    [Value _ _ _ (ForAll _ pty)] -> fromPredType identSupply pty
    _                          -> case qualLookupValue (qualQualify m f) tyEnv of
      [Value _ _ _ (ForAll _ pty)] -> fromPredType identSupply pty
      _                          ->
        internalError $ "GenAbstractCurry.getQualType: " ++ show f

getTypeVisibility :: Ident -> GAC CVisibility
getTypeVisibility i = S.gets $ \env ->
  if Set.member i (tyExports env) then Public else Private

getVisibility :: Ident -> GAC CVisibility
getVisibility i = S.gets $ \env ->
  if Set.member i (valExports env) then Public else Private

signatures :: [Decl a] -> [(Ident, QualTypeExpr)]
signatures ds = [(f, qty) | TypeSig _ fs qty <- ds, f <- fs]
