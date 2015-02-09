{- |
    Module      :  $Header$
    Description :  Generation of AbstractCurry program terms
    Copyright   :  (c) 2005       , Martin Engelke
                       2011 - 2015, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of an 'AbstractCurry' program term
    for a given 'Curry' module.
-}
module Generators.GenAbstractCurry (genAbstractCurry) where

import           Control.Applicative
import           Control.Monad              (replicateM)
import qualified Control.Monad.State as S   (State, evalState, get, gets, modify
                                            , put)
import qualified Data.Set            as Set (Set, empty, insert, member)
import qualified Data.Traversable    as T   (forM)

import Curry.AbstractCurry
import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.CurryTypes (fromType)
import Base.Expr       (bv)
import Base.Messages   (internalError)
import Base.NestEnv
import Base.Types      (TypeScheme (..))

import Env.Value       (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)
import Env.OpPrec      (mkPrec)

import CompilerEnv

type GAC a = S.State AbstractEnv a

-- ---------------------------------------------------------------------------
-- Interface
-- ---------------------------------------------------------------------------

-- |Generate an AbstractCurry program term from the syntax tree
genAbstractCurry :: CompilerEnv -> Module -> CurryProg
genAbstractCurry env mdl = S.evalState (trModule mdl) (abstractEnv env mdl)

-- ---------------------------------------------------------------------------
-- Conversion from Curry to AbstractCurry
-- ---------------------------------------------------------------------------

trModule :: Module -> GAC CurryProg
trModule (Module _ mid _ is ds) = do
  CurryProg mid' is' <$> ts' <*> tcs' <*> fs' <*> os'
  where
  mid'  = moduleName mid
  is'   = map cvImportDecl is
  tcs'  = concat <$> mapM (withLocalEnv . trTcDecl   ) ds
  ts'   = concat <$> mapM (withLocalEnv . trTypeDecl ) ds
  fs'   = concat <$> mapM (withLocalEnv . trFuncDecl ) ds
  os'   = concat <$> mapM (withLocalEnv . trInfixDecl) ds

cvImportDecl :: ImportDecl -> String
cvImportDecl (ImportDecl _ mid _ _ _) = moduleName mid

trTcDecl :: Decl -> GAC [CTypeClassDecl]
trTcDecl (ClassDecl _ cxt name var ds) = sequence $ return $
  CClassDecl <$> trLocalIdent name
             <*> getVisibility name
             <*> trSContext cxt
             <*> sequence (return (genTVarIndex var))
             <*> (mapM trFuncDecl ds >>= return . concat)
trTcDecl (InstanceDecl _ cxt qName tConstr _ ds) = sequence $ return $
  CInstanceDecl <$> trQual qName
                <*> trSContext cxt
                <*> trTypeConstr tConstr
                <*> (mapM trFuncDecl ds >>= return . concat)
trTcDecl _ = return []

trTypeConstr :: TypeConstructor -> GAC CTypeExpr
trTypeConstr UnitTC        = CTCons <$> trQual (preludeIdent "()") <*> return []
trTypeConstr (TupleTC n)   = do
  qName   <- trQual (preludeIdent "(,)")
  newVars <- replicateM n (freshVar "x")
  vars    <- mapM genTVarIndex newVars
  return $ CTCons qName (map CTVar vars)
trTypeConstr ListTC       =
  CTCons <$> trQual (preludeIdent "[]")
         <*> sequence (return (CTVar <$> (freshVar "x" >>= genTVarIndex)))
trTypeConstr ArrowTC      =
  CFuncType <$> (CTVar <$> (freshVar "x1" >>= genTVarIndex))
            <*> (CTVar <$> (freshVar "x2" >>= genTVarIndex))
trTypeConstr (QualTC qid) = CTCons <$> trQual qid <*> return []

trSContext :: SContext -> GAC CContext
trSContext (SContext cxs) = CContext <$>
  mapM (\(qid,ident) -> (,) <$> trQual qid
                            <*> (sequence $ return $ genTVarIndex ident)) cxs

trTypeDecl :: Decl -> GAC [CTypeDecl]
trTypeDecl (DataDecl    _ t vs cs _) = (\t' v vs' cs' -> [CType t' v vs' cs'])
  <$> trLocalIdent t <*> getVisibility t
  <*> mapM genTVarIndex vs <*> mapM trConsDecl cs
trTypeDecl (TypeDecl    _ t vs ty) = (\t' v vs' ty' -> [CTypeSyn t' v vs' ty'])
  <$> trLocalIdent t <*> getVisibility t
  <*> mapM genTVarIndex vs <*> trTypeExpr ty
trTypeDecl (NewtypeDecl _ t vs nc _) = (\t' v vs' nc' -> [CNewType t' v vs' nc'])
  <$> trLocalIdent t <*> getVisibility t
  <*> mapM genTVarIndex vs <*> trNewConsDecl nc
trTypeDecl _                       = return []

trConsDecl :: ConstrDecl -> GAC CConsDecl
trConsDecl (ConstrDecl      _ _ c tys) = CCons
  <$> trLocalIdent c <*> getVisibility c <*> mapM trTypeExpr tys
trConsDecl (ConOpDecl p vs ty1 op ty2) = trConsDecl $
  ConstrDecl p vs op [ty1, ty2]

trNewConsDecl :: NewConstrDecl -> GAC CConsDecl
trNewConsDecl (NewConstrDecl _ _ nc ty) = CCons
  <$> trLocalIdent nc <*> getVisibility nc <*> ((:[]) <$> trTypeExpr ty)

trTypeExpr :: TypeExpr -> GAC CTypeExpr
trTypeExpr (ConstructorType  q ts) = CTCons <$> trQual q
                                            <*> mapM trTypeExpr ts
trTypeExpr (SpecialConstructorType tConstr ts) =
  CTCons <$> trQual qName <*> mapM trTypeExpr ts
 where
  qName = case tConstr of
               QualTC qid -> qid
               _          -> preludeIdent (show tConstr)
trTypeExpr (VariableType        v) = CTVar  <$> getTVarIndex v
trTypeExpr (TupleType         tys) = trTypeExpr $ case tys of
   []   -> ConstructorType qUnitId []
   [ty] -> ty
   _    -> ConstructorType (qTupleId $ length tys) tys
trTypeExpr (ListType           ty) = trTypeExpr $ ConstructorType qListId [ty]
trTypeExpr (ArrowType     ty1 ty2) = CFuncType   <$> trTypeExpr ty1
                                                 <*> trTypeExpr ty2
-- FIX RECORDS
trTypeExpr (RecordType        fs) =
  CTCons <$> trLocalString "Record#" <*> mapM (trTypeExpr . snd) fs

trInfixDecl :: Decl -> GAC [COpDecl]
trInfixDecl (InfixDecl _ fix mprec ops) = mapM trInfix (reverse ops)
  where
  trInfix op = COp <$> trLocalIdent op <*> return (cvFixity fix)
                  <*> return (fromInteger (mkPrec mprec))
  cvFixity InfixL = CInfixlOp
  cvFixity InfixR = CInfixrOp
  cvFixity Infix  = CInfixOp
trInfixDecl _ = return []

trFuncDecl :: Decl -> GAC [CFuncDecl]
trFuncDecl (FunctionDecl _ mc' _ f eqs) = sequence $ return $
  CFunc <$> trLocalIdent f <*> getArity f <*> getVisibility f
        <*> trSContext (SContext cx)
        <*> (getType f >>= trTypeExpr)
        <*> mapM trEquation eqs
 where
  cx = case mc' of
    Nothing      -> []
    Just (cxt,_) -> map (\(qid,TypeVariable_ i) -> (qid, mkIdent (show i)))
                        (filter (isTypeVariable_ . snd) cxt)
  isTypeVariable_ (TypeVariable_ _) = True
  isTypeVariable_ _                 = False
trFuncDecl (ForeignDecl  _ _ _ f _) = (\f' a v cxt ty rs -> [CFunc f' a v cxt ty rs])
  <$> trLocalIdent f <*> getArity f <*> getVisibility f
  <*> return (CContext [])
  <*> (getType f >>= trTypeExpr)
  <*> return []
trFuncDecl (ExternalDecl      _ fs) = T.forM fs $ \f -> CFunc
  <$> trLocalIdent f <*> getArity f <*> getVisibility f
  <*> return (CContext [])
  <*> (getType f >>= trTypeExpr)
  <*> return []
trFuncDecl _                        = return []

trEquation :: Equation -> GAC CRule
trEquation (Equation _ lhs rhs) = inNestedScope
                                $ CRule <$> trLhs lhs <*> trRhs rhs

trLhs :: Lhs -> GAC [CPattern]
trLhs = mapM trPat . snd . flatLhs

trRhs :: Rhs -> GAC CRhs
trRhs (SimpleRhs _ e ds) = inNestedScope $ do
  mapM_ insertDeclLhs ds
  CSimpleRhs <$> trExpr e <*> (concat <$> mapM trLocalDecl ds)
trRhs (GuardedRhs gs ds) = inNestedScope $ do
  mapM_ insertDeclLhs ds
  CGuardedRhs <$> mapM trCondExpr gs <*> (concat <$> mapM trLocalDecl ds)

trCondExpr :: CondExpr -> GAC (CExpr, CExpr)
trCondExpr (CondExpr _ g e) = (,) <$> trExpr g <*> trExpr e

trLocalDecls :: [Decl] -> GAC [CLocalDecl]
trLocalDecls ds = do
  mapM_ insertDeclLhs ds
  concat <$> mapM trLocalDecl ds

insertDeclLhs :: Decl -> GAC ()
-- Insert all variables declared in local declarations
insertDeclLhs (PatternDecl  _ _ _ p _) = mapM_ genVarIndex (bv p)
insertDeclLhs (FreeDecl          _ vs) = mapM_ genVarIndex vs
insertDeclLhs _                        = return ()

trLocalDecl :: Decl -> GAC [CLocalDecl]
trLocalDecl f@(FunctionDecl _ _ _ _ _) = map CLocalFunc <$> trFuncDecl f
trLocalDecl f@(ForeignDecl  _ _ _ _ _) = map CLocalFunc <$> trFuncDecl f
trLocalDecl f@(ExternalDecl       _ _) = map CLocalFunc <$> trFuncDecl f
trLocalDecl (PatternDecl  _ _ _ p rhs) = (\p' rhs' -> [CLocalPat p' rhs'])
                                         <$> trPat p <*> trRhs rhs
trLocalDecl (FreeDecl            _ vs) = (\vs' -> [CLocalVars vs'])
                                         <$> mapM getVarIndex vs
trLocalDecl _                          = return [] -- can not occur (types etc.)

trContext :: Context -> GAC (CContext, [CTypeExpr])
trContext (Context cxs) = (,) <$> trSContext (SContext cPairs) <*> mapM trTypeExpr (concat tExprs)
 where
  (cPairs,tExprs)  = unzip $ map (\(ContextElem qid ident typeExprs) -> ((qid, ident), typeExprs)) cxs

trExpr :: Expression -> GAC CExpr
trExpr (Literal     l) = return (CLit $ cvLiteral l)
trExpr (Variable  _ v)
  | isQualified v = CSymbol <$> trQual v
  | otherwise     = lookupVarIndex v' >>= \mvi -> case mvi of
    Just vi -> return (CVar vi)
    _       -> CSymbol <$> trLocalIdent v'
  where v' = unqualify v
trExpr (Constructor c) = CSymbol <$> trQual c
trExpr (Paren       e) = trExpr e
trExpr (Typed _ e cxt ty) = do
  (cxt', _) <- trContext cxt
  CTyped <$> trExpr e <*> return cxt' <*> trTypeExpr ty
trExpr (Tuple    _ es) = trExpr $ case es of
  []  -> Variable Nothing qUnitId
  [x] -> x
  _   -> foldl Apply (Variable Nothing $ qTupleId $ length es) es
trExpr (List        _ es) = trExpr $
  foldr (Apply . Apply (Constructor qConsId)) (Constructor qNilId) es
trExpr (ListCompr _ e ds) = inNestedScope $ flip CListComp
                            <$> mapM trStatement ds <*> trExpr e
trExpr (EnumFrom       mc      e) = trExpr
                                 $ apply (Variable mc qEnumFromId      ) [e]
trExpr (EnumFromThen   mc  e1 e2) = trExpr
                                 $ apply (Variable mc qEnumFromThenId  ) [e1,e2]
trExpr (EnumFromTo     mc  e1 e2) = trExpr
                                 $ apply (Variable mc qEnumFromToId    ) [e1,e2]
trExpr (EnumFromThenTo mc e1 e2 e3) = trExpr
                                 $ apply (Variable mc qEnumFromThenToId) [e1,e2,e3]
trExpr (UnaryMinus       mc _ e) = trExpr $ apply (Variable mc qNegateId) [e]
trExpr (Apply             e1 e2) = CApply <$> trExpr e1 <*> trExpr e2
trExpr (InfixApply     e1 op e2) = trExpr $ apply (opToExpr op) [e1, e2]
trExpr (LeftSection        e op) = do
  v <- freshVar "x"
  trExpr $ Lambda noRef [VariablePattern v]
         $ Apply (Apply (opToExpr op) e) (Variable Nothing $ qualify v)
trExpr (RightSection       op e) = do
  v <- freshVar "x"
  trExpr $ Lambda noRef [VariablePattern v]
         $ Apply (Apply (opToExpr op) (Variable Nothing $ qualify v)) e
trExpr (Lambda           _ ps e) = inNestedScope $
                                   CLambda <$> mapM trPat ps <*> trExpr e
trExpr (Let                ds e) = inNestedScope $
                                   CLetDecl <$> trLocalDecls ds <*> trExpr e
trExpr (Do                 ss e) = inNestedScope $
                                   (\ss' e' -> CDoExpr (ss' ++ [CSExpr e']))
                                   <$> mapM trStatement ss <*> trExpr e
trExpr (IfThenElse   _ e1 e2 e3) = trExpr
                                 $ apply (Variable Nothing qIfThenElseId) [e1,e2,e3]
trExpr (Case          _ ct e bs) = CCase (cvCaseType ct)
                                   <$> trExpr e <*> mapM trAlt bs
-- FIX RECORDS
trExpr (RecordSelection e ident) = CApply <$> (CSymbol <$> trLocalIdent ident)
                                          <*> trExpr e
trExpr (RecordConstr         fs) = CRecConstr <$> trLocalString "Record#"
                                              <*> mapM (trField trExpr) fs
trExpr (RecordUpdate       fs e) = CRecUpdate <$> trExpr e
                                              <*> mapM (trField trExpr) fs

cvCaseType :: CaseType -> CCaseType
cvCaseType Flex  = CFlex
cvCaseType Rigid = CRigid

apply :: Expression -> [Expression] -> Expression
apply = foldl Apply

trStatement :: Statement -> GAC CStatement
trStatement (StmtExpr   _ e) = CSExpr     <$> trExpr e
trStatement (StmtDecl    ds) = CSLet      <$> trLocalDecls ds
trStatement (StmtBind _ p e) = flip CSPat <$> trExpr e <*> trPat p

trAlt :: Alt -> GAC (CPattern, CRhs)
trAlt (Alt _ p rhs) = inNestedScope $ (,) <$> trPat p <*> trRhs rhs

trPat :: Pattern -> GAC CPattern
trPat (LiteralPattern         l) = return (CPLit $ cvLiteral l)
trPat (VariablePattern        v) = CPVar <$> getVarIndex v
trPat (ConstructorPattern  c ps) = CPComb <$> trQual c <*> mapM trPat ps
trPat (InfixPattern    p1 op p2) = trPat $ ConstructorPattern op [p1, p2]
trPat (ParenPattern           p) = trPat p
trPat (TuplePattern        _ ps) = trPat $ case ps of
  []   -> ConstructorPattern qUnitId []
  [ty] -> ty
  _    -> ConstructorPattern (qTupleId $ length ps) ps
trPat (ListPattern         _ ps) = trPat $
  foldr (\x1 x2 -> ConstructorPattern qConsId [x1, x2])
        (ConstructorPattern qNilId [])
        ps
trPat (NegativePattern      _ l) = trPat $ LiteralPattern $ negateLiteral l
trPat (AsPattern            v p) = CPAs <$> getVarIndex v<*> trPat p
trPat (LazyPattern          _ p) = CPLazy <$> trPat p
trPat (FunctionPattern     f ps) = CPFuncComb <$> trQual f <*> mapM trPat ps
trPat (InfixFuncPattern p1 f p2) = trPat (FunctionPattern f [p1, p2])
-- FIX RECORDS
trPat (RecordPattern      fs _) =
 CPRecord <$> trLocalString "Record#" <*> mapM (trField trPat) fs

trField :: (a -> GAC b) -> Field a -> GAC (CField b)
trField act (Field _ l x) = (,) <$> return (idName l) <*> act x

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
  | isPreludeSymbol qid = return $ cvQualIdent $ qualQualify preludeMIdent qid
  | isQualified     qid = return $ cvQualIdent $ qid
  | otherwise           = S.gets $ \env -> cvQualIdent $
                          case lookupValue i (typeEnv env) of
                            [info] -> origName info
                            _      -> qualifyWith (moduleId env) i
  where i = unqualify qid

trLocalIdent :: Ident -> GAC QName
trLocalIdent i = S.get >>= \env -> return (moduleName $ moduleId env, idName i)

trLocalString :: String -> GAC QName
trLocalString str = S.get >>= \env -> return (moduleName $ moduleId env, str)

cvQualIdent :: QualIdent -> QName
cvQualIdent qid = case qidModule qid of
  Just m -> (moduleName m, idName $ qidIdent qid)
  _      -> internalError $ "GenAbstractCurry.cvQualIdent: " ++ show qid

-- Converts an infix operator to an expression
opToExpr :: InfixOp -> Expression
opToExpr (InfixOp mCType op) = Variable    mCType op
opToExpr (InfixConstr     c) = Constructor c

qEnumFromId :: QualIdent
qEnumFromId = preludeIdent "enumFrom"

qEnumFromThenId :: QualIdent
qEnumFromThenId = preludeIdent "enumFromThen"

qEnumFromToId :: QualIdent
qEnumFromToId = preludeIdent "enumFromTo"

qEnumFromThenToId :: QualIdent
qEnumFromThenToId = preludeIdent "enumFromThenTo"

qNegateId :: QualIdent
qNegateId = preludeIdent "negate"

qIfThenElseId :: QualIdent
qIfThenElseId = preludeIdent "if_then_else"

preludeIdent :: String -> QualIdent
preludeIdent = qualifyWith preludeMIdent . mkIdent

-- Checks, whether a symbol is defined in the Prelude.
isPreludeSymbol :: QualIdent -> Bool
isPreludeSymbol qid
  = let (mmid, ident) = (qidModule qid, qidIdent qid)
    in   mmid == Just preludeMIdent
      || elem ident [unitId, listId, nilId, consId]
      || isTupleId ident

-------------------------------------------------------------------------------
-- This part defines an environment containing all necessary information
-- for generating the AbstractCurry representation of a CurrySyntax term.

-- |Data type for representing an AbstractCurry generator environment
data AbstractEnv = AbstractEnv
  { moduleId   :: ModuleIdent         -- ^name of the module
  , typeEnv    :: ValueEnv            -- ^known values
  , exports    :: Set.Set Ident       -- ^exported symbols
  , varIndex   :: Int                 -- ^counter for variable indices
  , tvarIndex  :: Int                 -- ^counter for type variable indices
  , varEnv     :: NestEnv Int         -- ^stack of variable tables
  , tvarEnv    :: TopEnv Int          -- ^stack of type variable tables
  } deriving Show

-- |Initialize the AbstractCurry generator environment
abstractEnv :: CompilerEnv -> Module -> AbstractEnv
abstractEnv env (Module _ mid es _ _) = AbstractEnv
  { moduleId  = mid
  , typeEnv   = valueEnv env
  , exports   = foldr (buildExportTable mid) Set.empty es'
  , varIndex  = 0
  , tvarIndex = 0
  , varEnv  = globalEnv emptyTopEnv
  , tvarEnv = emptyTopEnv
  }
  where es' = case es of
          Just (Exporting _ e) -> e
          _                    -> internalError "GenAbstractCurry.abstractEnv"

-- Builds a table containing all exported identifiers from a module.
buildExportTable :: ModuleIdent -> Export -> Set.Set Ident -> Set.Set Ident
buildExportTable mid (Export             q)
  | isLocalIdent mid q  = Set.insert (unqualify q)
buildExportTable mid (ExportTypeWith tc cs)
  | isLocalIdent mid tc = flip (foldr Set.insert) (unqualify tc : cs)
buildExportTable _   _  = id

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

-- Generates an identifier which doesn't occur in the variable table
-- of the current scope.
freshVar :: String -> GAC Ident
freshVar vname = S.gets $ genFreshVar 0 . varEnv
  where
  genFreshVar :: Int -> NestEnv a -> Ident
  genFreshVar idx vs
    | elemNestEnv ident vs = genFreshVar (idx + 1) vs
    | otherwise            = ident
    where ident = mkIdent $ vname ++ show idx

-- Looks up the unique index for the type variable 'ident' in the type
-- variable table of the current scope.
getTVarIndex :: Ident -> GAC CTVarIName
getTVarIndex i = S.get >>= \env -> case lookupTopEnv i $ tvarEnv env of
  [v] -> return (v, idName i)
  _   -> genTVarIndex i

-- Generates an unique index for the type variable 'ident' and inserts it
-- into the type variable table of the current scope.
genTVarIndex :: Ident -> GAC CTVarIName
genTVarIndex i = do
  env <- S.get
  let idx = tvarIndex env
  S.put $ env {tvarIndex = idx + 1, tvarEnv = bindTopEnv i idx (tvarEnv env)}
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
  S.modify $ \e -> e { varEnv = nestEnv $ vo, tvarEnv = emptyTopEnv }
  res <- act
  S.modify $ \e -> e { varEnv = vo, tvarEnv = to }
  return res

getArity :: Ident -> GAC Int
getArity f = do
  m     <- S.gets moduleId
  tyEnv <- S.gets typeEnv
  return $ case lookupValue f tyEnv of
    [Value _ a _ _] -> a
    _             -> case qualLookupValue (qualifyWith m f) tyEnv of
      [Value _ a _ _] -> a
      _             -> internalError $ "GenAbstractCurry.getArity: " ++ show f

getType :: Ident -> GAC TypeExpr
getType f = do
  m     <- S.gets moduleId
  tyEnv <- S.gets typeEnv
  return $ case lookupValue f tyEnv of
    [Value _ _ (ForAll _ _ ty) _ ] -> fromType ty
    _ -> case qualLookupValue (qualifyWith m f) tyEnv of
      [Value _ _ (ForAll _ _ ty) _] -> fromType ty
      _ -> internalError $ "GenAbstractCurry.getType: " ++ show f

getVisibility :: Ident -> GAC CVisibility
getVisibility i = S.gets $ \env -> if Set.member i (exports env) then Public
                                                                 else Private
