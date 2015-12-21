-- ---------------------------------------------------------------------------
--
-- GenFlatCurry - Generates FlatCurry program terms and FlatCurry interfaces
--                (type 'FlatCurry.Prog')
--
-- November 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
-- ---------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
module Generators.GenFlatCurry (genFlatCurry, genFlatInterface) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative ((<$>), (<*>))
#endif
import           Control.Monad       (filterM, mplus)
import           Control.Monad.State (State, evalState, gets, modify)
import           Data.List           (mapAccumL, nub)
import qualified Data.Map as Map     (Map, empty, insert, lookup, fromList, toList)
import           Data.Maybe          (fromMaybe, isJust)

import           Curry.Base.Ident
import           Curry.ExtendedFlat.Type
import qualified Curry.Syntax as CS

import Base.CurryTypes
import Base.Messages (internalError)
import Base.ScopeEnv (ScopeEnv)
import qualified Base.ScopeEnv as SE (new, insert, lookup, beginScope, endScope)
import Base.TopEnv (topEnvMap)
import Base.Types

import Env.Interface
import Env.TypeConstructor (TCEnv, TypeInfo (..))
import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

import qualified IL as IL
import qualified ModuleSummary
import Transformations (transType)

-------------------------------------------------------------------------------

-- transforms intermediate language code (IL) to FlatCurry code
genFlatCurry :: ModuleSummary.ModuleSummary -> InterfaceEnv
             -> ValueEnv -> TCEnv -> IL.Module -> Prog
genFlatCurry modSum mEnv tyEnv tcEnv mdl = patchPrelude $
  run modSum mEnv tyEnv tcEnv False (trModule mdl)

-- transforms intermediate language code (IL) to FlatCurry interfaces
genFlatInterface :: ModuleSummary.ModuleSummary -> InterfaceEnv
                 -> ValueEnv -> TCEnv -> IL.Module -> Prog
genFlatInterface modSum mEnv tyEnv tcEnv mdl = patchPrelude $
  run modSum mEnv tyEnv tcEnv True (trInterface mdl)

patchPrelude :: Prog -> Prog
patchPrelude p@(Prog n _ types funcs ops)
  | n == prelude = Prog n [] (preludeTypes ++ types) funcs ops
  | otherwise    = p

preludeTypes :: [TypeDecl]
preludeTypes =
  [ Type unit Public [] [(Cons unit 0 Public [])]
  , Type nil Public [0]
    [ Cons nil  0 Public []
    , Cons cons 2 Public [TVar 0, TCons nil [TVar 0]]
    ]
  ] ++ map mkTupleType [2 .. maxTupleArity]
  where unit = mkPreludeQName "()"
        nil  = mkPreludeQName "[]"
        cons = mkPreludeQName ":"

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

-- ---------------------------------------------------------------------------

-- The environment 'FlatEnv' is embedded in the monadic representation
-- 'FlatState' which allows the usage of 'do' expressions.
type FlatState a = State FlatEnv a

-- Data type for representing an environment which contains information needed
-- for generating FlatCurry code.
data FlatEnv = FlatEnv
  { moduleIdE     :: ModuleIdent
  , interfaceEnvE :: InterfaceEnv
  , typeEnvE      :: ValueEnv     -- types of defined values
  , tConsEnvE     :: TCEnv
  , publicEnvE    :: Map.Map Ident IdentExport
  , fixitiesE     :: [CS.IDecl]
  , typeSynonymsE :: [CS.IDecl]
  , importsE      :: [CS.IImportDecl]
  , exportsE      :: [CS.Export]
  , interfaceE    :: [CS.IDecl]
  , varIndexE     :: Int
  , varIdsE       :: ScopeEnv Ident VarIndex
  , genInterfaceE :: Bool
  , localTypes    :: Map.Map QualIdent IL.Type
  , consTypes     :: Map.Map QualIdent IL.Type
  }

data IdentExport
  = NotConstr     -- function, type-constructor
  | OnlyConstr    -- constructor
  | NotOnlyConstr -- constructor, function, type-constructor

-- Runs a 'FlatState' action and returns the result
run :: ModuleSummary.ModuleSummary -> InterfaceEnv -> ValueEnv -> TCEnv
    -> Bool -> FlatState a -> a
run modSum mEnv tyEnv tcEnv genIntf f = evalState f env0
  where
  env0 = FlatEnv
    { moduleIdE     = ModuleSummary.moduleId modSum
    , interfaceEnvE = mEnv
    , typeEnvE      = tyEnv
    , tConsEnvE     = tcEnv
    , publicEnvE    = genPubEnv (ModuleSummary.moduleId  modSum)
                                (ModuleSummary.interface modSum)
    , fixitiesE     = ModuleSummary.infixDecls   modSum
    , typeSynonymsE = ModuleSummary.typeSynonyms modSum
    , importsE      = ModuleSummary.imports      modSum
    , exportsE      = ModuleSummary.exports      modSum
    , interfaceE    = ModuleSummary.interface    modSum
    , varIndexE     = 0
    , varIdsE       = SE.new
    , genInterfaceE = genIntf
    , localTypes    = Map.empty
    , consTypes     = Map.fromList $ getConstrTypes tcEnv
    }

getConstrTypes :: TCEnv -> [(QualIdent, IL.Type)]
getConstrTypes tcEnv =
  [ mkConstrType tqid conid argtys argc
  | (_, (_, DataType tqid argc dts):_) <- Map.toList $ topEnvMap tcEnv
  , (DataConstr conid _ argtys) <- dts
  ]
  where
  mkConstrType tqid conid argtypes targnum = (conname, contype)
    where
    conname    = QualIdent (qidModule tqid) conid
    resty = IL.TypeConstructor tqid (map IL.TypeVariable [0 .. targnum - 1])
    contype    = foldr IL.TypeArrow resty $ map ttrans argtypes

trModule :: IL.Module -> FlatState Prog
trModule (IL.Module mid imps ds) = do
  -- insert local decls into localDecls
  modify $ \ s -> s { localTypes = Map.fromList [ (qn, t) | IL.FunctionDecl qn _ t _ <- ds ] }
  is      <- (\is -> map moduleName $ nub $ imps ++ map extractMid is) <$> imports
  types   <- genTypeSynonyms
  tyds    <- concat <$> mapM trTypeDecl ds
  funcs   <- concat <$> mapM trFuncDecl ds
  ops     <- genOpDecls
  return $ Prog (moduleName mid) is (types ++ tyds) funcs ops
  where extractMid (CS.IImportDecl _ mid1) = mid1

trInterface :: IL.Module -> FlatState Prog
trInterface (IL.Module mid imps decls) = do
  -- insert local decls into localDecls
  modify $ \ s -> s { localTypes = Map.fromList [ (qn, t) | IL.FunctionDecl qn _ t _ <- decls ] }
  is      <- (\is -> map moduleName $ nub $ imps ++ map extractMid is) <$> imports
  expimps <- getExportedImports
  itypes  <- mapM trITypeDecl (filter isTypeIDecl expimps)
  types   <- genTypeSynonyms
  datas   <- filterM isPublicDataDecl    decls >>= concatMapM trTypeDecl
  newtys  <- filterM isPublicNewtypeDecl decls >>= concatMapM trTypeDecl
  ifuncs  <- mapM trIFuncDecl (filter isFuncIDecl expimps)
  funcs   <- filterM isPublicFuncDecl    decls >>= concatMapM trFuncDecl
  iops    <- mapM trIOpDecl (filter isOpIDecl expimps)
  ops     <- genOpDecls
  return $ Prog (moduleName mid) is (itypes ++ types ++ datas ++ newtys)
                          (ifuncs ++ funcs) (iops ++ ops)
  where extractMid (CS.IImportDecl _ mid1) = mid1

concatMapM :: (Functor m, Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM act xs = concat <$> mapM act xs

trTypeDecl :: IL.Decl -> FlatState [TypeDecl]
trTypeDecl (IL.DataDecl qid arity cs) = ((:[]) <$>) $
  Type  <$> trTypeIdent qid
        <*> getVisibility False qid <*> return [0 .. arity - 1]
        <*> (concat <$> mapM trConstrDecl cs)
trTypeDecl (IL.NewtypeDecl qid arity (IL.ConstrDecl _ ty)) = ((:[]) <$>) $
  TypeSyn <$> trTypeIdent qid <*> getVisibility False qid
          <*> return [0 .. arity - 1] <*> trType ty
trTypeDecl _ = return []

trConstrDecl :: IL.ConstrDecl [IL.Type] -> FlatState [ConsDecl]
trConstrDecl (IL.ConstrDecl qid tys) = do
  qid' <- trQualIdent qid
  vis  <- getVisibility True qid
  tys' <- mapM trType tys
  let flatCons = Cons qid' (length tys) vis tys'
  whenFlatCurry (return [flatCons]) (return [flatCons | vis == Public]) -- TODO: whenFlatCurry

trType :: IL.Type -> FlatState TypeExpr
trType (IL.TypeConstructor t tys) = TCons <$> trTypeIdent t <*> mapM trType tys
trType (IL.TypeVariable      idx) = return $ TVar $ abs idx
trType (IL.TypeArrow     ty1 ty2) = FuncType <$> trType ty1 <*> trType ty2

trFuncDecl :: IL.Decl -> FlatState [FuncDecl]
trFuncDecl (IL.FunctionDecl qid vs ty e) = do
  qname <- trQualIdent qid
  arity <- getArity qid
  texpr <- trType ty
  whenFlatCurry
    (do vis   <- getVisibility False qid
        is    <- mapM newVarIndex vs
        expr  <- trExpr e
        clearVarIndices
        return [Func qname arity vis texpr (Rule is expr)]
    )
    (return [Func qname arity Public texpr (Rule [] (Var $ mkIdx 0))])
trFuncDecl (IL.ExternalDecl qid _ extname ty) = do
  texpr <- trType ty
  qname <- trQualIdent qid
  arity <- getArity qid
  vis   <- getVisibility False qid
  xname <- trExternal extname
  return [Func qname arity vis texpr (External xname)]
trFuncDecl _ = return []

trExpr :: IL.Expression -> FlatState Expr
trExpr (IL.Literal       l) = Lit <$> trLiteral l
trExpr (IL.Variable      v) = Var <$> lookupVarIndex v
trExpr (IL.Function    f _) = do
  qname <- trQualIdent f
  arity <- getArity    f
  genFuncCall qname arity []
trExpr (IL.Constructor c _) = do
  qname <- trQualIdent c
  arity <- getArity    c
  genConsCall qname arity []
trExpr (IL.Apply     e1 e2) = trApply e1 e2
trExpr (IL.Case   r t e bs) = Case r (cvEval t) <$> trExpr e <*> mapM trAlt bs
trExpr (IL.Or        e1 e2) = Or <$> trExpr e1 <*> trExpr e2
trExpr (IL.Exist       v e) = do
  idx <- newVarIndex v
  e'  <- trExpr e
  return $ case e' of
    Free is e'' -> Free (idx : is) e''
    _           -> Free (idx : []) e'
trExpr (IL.Let (IL.Binding v b) e) = inNewScope $ do
  v' <- newVarIndex v
  b' <- trExpr b
  e' <- trExpr e
  return $ case e' of -- TODO bjp(2011-09-21): maybe remove again, ask @MH
    Let bs e'' -> Let ((v', b'):bs) e''
    _          -> Let ((v', b'):[]) e'
trExpr (IL.Letrec   bs e) = inNewScope $ do
  let (vs, es) = unzip [ (v, b) | IL.Binding v b <- bs]
  vs' <- mapM newVarIndex vs
  es' <- mapM trExpr es
  e'  <- trExpr e
  return $ Let (zip vs' es') e'
trExpr (IL.Typed e ty) = Typed <$> trExpr e <*> trType ty

trLiteral :: IL.Literal -> FlatState Literal
trLiteral (IL.Char  rs c) = return $ Charc  rs c
trLiteral (IL.Int   rs i) = return $ Intc   rs i
trLiteral (IL.Float rs f) = return $ Floatc rs f

trAlt :: IL.Alt -> FlatState BranchExpr
trAlt (IL.Alt p e) = Branch <$> trPat p <*> trExpr e

trPat :: IL.ConstrTerm -> FlatState Pattern
trPat (IL.LiteralPattern        l) = LPattern <$> trLiteral l
trPat (IL.ConstructorPattern c vs) = Pattern  <$> trQualIdent c
                                              <*> mapM newVarIndex vs
trPat (IL.VariablePattern       _) = internalError "GenFlatCurry.trPat"

cvEval :: IL.Eval -> CaseType
cvEval IL.Rigid = Rigid
cvEval IL.Flex  = Flex

-------------------------------------------------------------------------------

trIFuncDecl :: CS.IDecl -> FlatState FuncDecl
trIFuncDecl (CS.IFunctionDecl _ f a ty) = do
  texpr <- trType $ snd $ cs2ilType [] ty
  qname <- trQualIdent f
  return $ Func qname a Public texpr (Rule [] (Var $ mkIdx 0))
trIFuncDecl _ = internalError "GenFlatCurry: no function interface"

trITypeDecl :: CS.IDecl -> FlatState TypeDecl
trITypeDecl (CS.IDataDecl _ t vs cs hs) = do
  let mid = fromMaybe (internalError "GenFlatCurry: no module name") (qidModule t)
      is  = [0 .. length vs - 1]
  cdecls <- mapM (visitConstrIDecl mid $ zip vs is)
                 [c | c <- cs, CS.constrId c `notElem` hs]
  qname  <- trTypeIdent t
  return $ Type qname Public is cdecls
trITypeDecl (CS.ITypeDecl _ t vs ty) = do
  let is = [0 .. length vs - 1]
  ty'   <- trType $ snd $ cs2ilType (zip vs is) ty
  qname <- trTypeIdent t
  return $ TypeSyn qname Public is ty'
trITypeDecl _ = internalError "GenFlatCurry: no type interface"

visitConstrIDecl :: ModuleIdent -> [(Ident, Int)] -> CS.ConstrDecl
                 -> FlatState ConsDecl
visitConstrIDecl mid tis (CS.ConstrDecl _ _ ident typeexprs) = do
  texprs <- mapM (trType . (snd . cs2ilType tis)) typeexprs
  qname  <- trQualIdent (qualifyWith mid ident)
  return (Cons qname (length typeexprs) Public texprs)
visitConstrIDecl mid tis (CS.ConOpDecl pos ids type1 ident type2)
  = visitConstrIDecl mid tis (CS.ConstrDecl pos ids ident [type1,type2])
visitConstrIDecl mid tis (CS.RecordDecl _ _ ident fs) = do
  texprs <- mapM (trType . (snd . cs2ilType tis)) tys
  qname  <- trQualIdent (qualifyWith mid ident)
  return (Cons qname (length tys) Public texprs)
  where tys = [ty | CS.FieldDecl _ ls ty <- fs, _ <- ls]

trIOpDecl :: CS.IDecl -> FlatState OpDecl
trIOpDecl (CS.IInfixDecl _ fixi prec op) = do
  op' <- trQualIdent op
  return $ Op op' (genFixity fixi) prec
trIOpDecl _ = internalError "GenFlatCurry.trIOpDecl: no pattern match"

-------------------------------------------------------------------------------

trQualIdent :: QualIdent -> FlatState QName
trQualIdent qid = do
  mid <- getModuleIdent
  let (mmod, ident) = (qidModule qid, qidIdent qid)
      modid | elem ident [listId, consId, nilId, unitId] || isTupleId ident
            = moduleName preludeMIdent
            | otherwise
            = maybe (moduleName mid) moduleName mmod
  ftype <- lookupIdType qid
  return (QName Nothing ftype modid $ idName ident)

-- This variant of trQualIdent does not look up the type of the identifier,
-- which is wise when the identifier is bound to a type, because looking up
-- the type of a type via lookupIdType will get stuck in an endless loop. (hsi)
trTypeIdent :: QualIdent -> FlatState QName
trTypeIdent qid = do
  mid <- getModuleIdent
  let (mmod, ident) = (qidModule qid, qidIdent qid)
      modid | elem ident [listId, consId, nilId, unitId] || isTupleId ident
            = moduleName preludeMIdent
            | otherwise
            = maybe (moduleName mid) moduleName mmod
  return (QName Nothing Nothing modid $ idName ident)

trExternal :: String -> FlatState String
trExternal extname
  = getModuleIdent >>= \mid -> return (moduleName mid ++ "." ++ extname)

getVisibility :: Bool -> QualIdent -> FlatState Visibility
getVisibility isConstr qid = do
  public <- isPublic isConstr qid
  return $ if public then Public else Private

getExportedImports :: FlatState [CS.IDecl]
getExportedImports = do
  mid  <- getModuleIdent
  exps <- exports
  genExportedIDecls $ Map.toList $ getExpImports mid Map.empty exps

getExpImports :: ModuleIdent -> Map.Map ModuleIdent [CS.Export] -> [CS.Export]
              -> Map.Map ModuleIdent [CS.Export]
getExpImports _      expenv [] = expenv
getExpImports mident expenv ((CS.Export qid):exps)
  = getExpImports mident
    (bindExpImport mident qid (CS.Export qid) expenv)
    exps
getExpImports mident expenv ((CS.ExportTypeWith qid idents):exps)
  = getExpImports mident
    (bindExpImport mident qid (CS.ExportTypeWith qid idents) expenv)
    exps
getExpImports mident expenv ((CS.ExportTypeAll qid):exps)
  = getExpImports mident
    (bindExpImport mident qid (CS.ExportTypeAll qid) expenv)
    exps
getExpImports mident expenv ((CS.ExportModule mident'):exps)
  = getExpImports mident (Map.insert mident' [] expenv) exps

bindExpImport :: ModuleIdent -> QualIdent -> CS.Export
              -> Map.Map ModuleIdent [CS.Export]
              -> Map.Map ModuleIdent [CS.Export]
bindExpImport mident qid export expenv
  | isJust (localIdent mident qid)
  = expenv
  | otherwise
  = let (Just modid) = qidModule qid
    in  maybe (Map.insert modid [export] expenv)
              (\es -> Map.insert modid (export:es) expenv)
              (Map.lookup modid expenv)

genExportedIDecls :: [(ModuleIdent,[CS.Export])] -> FlatState [CS.IDecl]
genExportedIDecls mes = genExpIDecls [] mes

genExpIDecls :: [CS.IDecl] -> [(ModuleIdent,[CS.Export])] -> FlatState [CS.IDecl]
genExpIDecls idecls [] = return idecls
genExpIDecls idecls ((mid,exps):mes) = do
  intf_ <- lookupModuleIntf mid
  let idecls' = maybe idecls (p_genExpIDecls mid idecls exps) intf_
  genExpIDecls idecls' mes
 where
  p_genExpIDecls mid1 idecls1 exps1 (CS.Interface _ _ ds)
    | null exps1 = (map (qualifyIDecl mid1) ds) ++ idecls1
    | otherwise = filter (isExportedIDecl exps1) (map (qualifyIDecl mid1) ds)
                  ++ idecls1

isExportedIDecl :: [CS.Export] -> CS.IDecl -> Bool
isExportedIDecl exprts (CS.IInfixDecl _ _ _ qid)
  = isExportedQualIdent qid exprts
isExportedIDecl exprts (CS.IDataDecl _ qid _ _ _)
  = isExportedQualIdent qid exprts
isExportedIDecl exprts (CS.ITypeDecl _ qid _ _)
  = isExportedQualIdent qid exprts
isExportedIDecl exprts (CS.IFunctionDecl _ qid _ _)
  = isExportedQualIdent qid exprts
isExportedIDecl _ _ = False

isExportedQualIdent :: QualIdent -> [CS.Export] -> Bool
isExportedQualIdent _ [] = False
isExportedQualIdent qid ((CS.Export qid'):exps)
  = qid == qid' || isExportedQualIdent qid exps
isExportedQualIdent qid ((CS.ExportTypeWith qid' _):exps)
  = qid == qid' || isExportedQualIdent qid exps
isExportedQualIdent qid ((CS.ExportTypeAll qid'):exps)
  = qid == qid' || isExportedQualIdent qid exps
isExportedQualIdent qid ((CS.ExportModule _):exps)
  = isExportedQualIdent qid exps

qualifyIDecl :: ModuleIdent -> CS.IDecl -> CS.IDecl
qualifyIDecl mid (CS.IInfixDecl   pos fixi prec qid)
  = CS.IInfixDecl pos fixi prec (qualQualify mid qid)
qualifyIDecl mid (CS.IDataDecl    pos qid vs cs hs)
  = CS.IDataDecl pos (qualQualify mid qid) vs
    (map (qualifyIConstrDecl mid) cs) hs
qualifyIDecl mid (CS.INewtypeDecl  pos qid vs nc hs)
  = CS.INewtypeDecl pos (qualQualify mid qid) vs nc hs
qualifyIDecl mid (CS.ITypeDecl     pos qid vs ty)
  = CS.ITypeDecl pos (qualQualify mid qid) vs ty
qualifyIDecl mid (CS.IFunctionDecl pos qid arity ty)
  = CS.IFunctionDecl pos (qualQualify mid qid) arity (qualifyCSType mid ty)
qualifyIDecl _ idecl = idecl

qualifyIConstrDecl :: ModuleIdent -> CS.ConstrDecl -> CS.ConstrDecl
qualifyIConstrDecl mid (CS.ConstrDecl pos vs cid tys)
  = CS.ConstrDecl pos vs cid (map (qualifyCSType mid) tys)
qualifyIConstrDecl mid (CS.ConOpDecl pos vs ty1 op ty2)
  = CS.ConOpDecl pos vs (qualifyCSType mid ty1) op (qualifyCSType mid ty2)
qualifyIConstrDecl mid (CS.RecordDecl pos vs cid fs)
  = CS.RecordDecl pos vs cid (map (qualifyFieldDecl mid) fs)

qualifyFieldDecl :: ModuleIdent -> CS.FieldDecl -> CS.FieldDecl
qualifyFieldDecl m (CS.FieldDecl p l ty) = CS.FieldDecl p l (qualifyCSType m ty)

qualifyCSType :: ModuleIdent -> CS.TypeExpr -> CS.TypeExpr
qualifyCSType mid = fromType . toQualType mid []

trApply :: IL.Expression -> IL.Expression -> FlatState Expr
trApply e1 e2 = genFlatApplic [e2] e1
  where
  genFlatApplic es e = case e of
    (IL.Apply     ea eb) -> genFlatApplic (eb:es) ea
    (IL.Function    f _) -> do
      qname <- trQualIdent f
      arity <- getArity f
      genFuncCall qname arity es
    (IL.Constructor c _) -> do
      qname <- trQualIdent c
      arity <- getArity c
      genConsCall qname arity es
    _ -> do
      expr <- trExpr e
      genApplicComb expr es

genFuncCall :: QName -> Int -> [IL.Expression] -> FlatState Expr
genFuncCall qname arity es
  | cnt <  arity = genComb qname es (FuncPartCall (arity - cnt))
  | cnt == arity = genComb qname es FuncCall
  | otherwise    = do
    let (es1, es2) = splitAt arity es
    funccall <- genComb qname es1 FuncCall
    genApplicComb funccall es2
 where cnt = length es

genConsCall :: QName -> Int -> [IL.Expression] -> FlatState Expr
genConsCall qname arity es
  | cnt <  arity = genComb qname es (ConsPartCall (arity - cnt))
  | cnt == arity = genComb qname es ConsCall
  | otherwise    = do
    let (es1, es2) = splitAt arity es
    conscall <- genComb qname es1 ConsCall
    genApplicComb conscall es2
 where cnt = length es

genComb :: QName -> [IL.Expression] -> CombType -> FlatState Expr
genComb qid es ct = Comb ct qid <$> mapM trExpr es

genApplicComb :: Expr -> [IL.Expression] -> FlatState Expr
genApplicComb e []      = return e
genApplicComb e (e1:es) = do
  expr1 <- trExpr e1
  qname <- trQualIdent qidApply
  genApplicComb (Comb FuncCall qname [e, expr1]) es
  where
  qidApply = qualifyWith preludeMIdent (mkIdent "apply")

genOpDecls :: FlatState [OpDecl]
genOpDecls = fixities >>= mapM genOpDecl

genOpDecl :: CS.IDecl -> FlatState OpDecl
genOpDecl (CS.IInfixDecl _ fix prec qid) = do
  qname <- trQualIdent qid
  return $ Op qname (genFixity fix) prec
genOpDecl _ = internalError "GenFlatCurry: no infix interface"

genFixity :: CS.Infix -> Fixity
genFixity CS.InfixL = InfixlOp
genFixity CS.InfixR = InfixrOp
genFixity CS.Infix  = InfixOp

-- The intermediate language (IL) does not represent type synonyms.
-- For this reason an interface representation of all type synonyms is generated
-- from the abstract syntax representation of the Curry program.
-- The function 'typeSynonyms' returns this list of type synonyms.
genTypeSynonyms ::  FlatState [TypeDecl]
genTypeSynonyms = typeSynonyms >>= mapM genTypeSynonym

genTypeSynonym :: CS.IDecl -> FlatState TypeDecl
genTypeSynonym (CS.ITypeDecl _ qid tvs ty) = do
  qname <- trTypeIdent qid
  vis   <- getVisibility False qid
  let vs = [0 .. length tvs - 1]
  ty'   <- trType $ snd $ cs2ilType (zip tvs vs) ty
  return $ TypeSyn qname vis vs ty'
genTypeSynonym _ = internalError "GenFlatCurry: no type synonym interface"

cs2ilType :: [(Ident,Int)] -> CS.TypeExpr -> ([(Ident,Int)], IL.Type)
cs2ilType ids (CS.ConstructorType qid typeexprs)
  = let (ids', ilTypeexprs) = mapAccumL cs2ilType ids typeexprs
    in  (ids', IL.TypeConstructor qid ilTypeexprs)
cs2ilType ids (CS.VariableType ident) = case lookup ident ids of
  Just i  -> (ids, IL.TypeVariable i)
  Nothing -> let nid = 1 + case ids of { [] -> 0; (_, j):_ -> j }
             in  ((ident, nid):ids, IL.TypeVariable nid)
cs2ilType ids (CS.ArrowType type1 type2)
  = let (ids',  ilType1) = cs2ilType ids type1
        (ids'', ilType2) = cs2ilType ids' type2
    in  (ids'', IL.TypeArrow ilType1 ilType2)
cs2ilType ids (CS.ListType typeexpr)
  = let (ids', ilTypeexpr) = cs2ilType ids typeexpr
    in  (ids', IL.TypeConstructor (qualify listId) [ilTypeexpr])
cs2ilType ids (CS.TupleType typeexprs)
  = case typeexprs of
    []  -> (ids, IL.TypeConstructor qUnitId [])
    [t] -> cs2ilType ids t
    _   -> let (ids', ilTypeexprs) = mapAccumL cs2ilType ids typeexprs
               tuplen = length ilTypeexprs
           in  (ids', IL.TypeConstructor (qTupleId tuplen) ilTypeexprs)
cs2ilType ids (CS.ParenType ty) = cs2ilType ids ty

isPublicDataDecl :: IL.Decl -> FlatState Bool
isPublicDataDecl (IL.DataDecl qid _ _) = isPublic False qid
isPublicDataDecl _                     = return False

isPublicNewtypeDecl :: IL.Decl -> FlatState Bool
isPublicNewtypeDecl (IL.NewtypeDecl qid _ _) = isPublic False qid
isPublicNewtypeDecl _                        = return False

isPublicFuncDecl :: IL.Decl -> FlatState Bool
isPublicFuncDecl (IL.FunctionDecl qid _ _ _) = isPublic False qid
isPublicFuncDecl (IL.ExternalDecl qid _ _ _) = isPublic False qid
isPublicFuncDecl _                           = return False

isTypeIDecl :: CS.IDecl -> Bool
isTypeIDecl (CS.IDataDecl _ _ _ _ _) = True
isTypeIDecl (CS.ITypeDecl   _ _ _ _) = True
isTypeIDecl _                        = False

isFuncIDecl :: CS.IDecl -> Bool
isFuncIDecl (CS.IFunctionDecl _ _ _ _) = True
isFuncIDecl _                          = False

isOpIDecl :: CS.IDecl -> Bool
isOpIDecl (CS.IInfixDecl _ _ _ _) = True
isOpIDecl _                       = False

getModuleIdent :: FlatState ModuleIdent
getModuleIdent = gets moduleIdE

exports :: FlatState [CS.Export]
exports = gets exportsE

imports :: FlatState [CS.IImportDecl]
imports = gets importsE

fixities :: FlatState [CS.IDecl]
fixities = gets fixitiesE

typeSynonyms :: FlatState [CS.IDecl]
typeSynonyms = gets typeSynonymsE

isPublic :: Bool -> QualIdent -> FlatState Bool
isPublic isConstr qid = gets $ \ s -> maybe False isP
  (Map.lookup (unqualify qid) $ publicEnvE s)
  where
  isP NotConstr     = not isConstr
  isP OnlyConstr    = isConstr
  isP NotOnlyConstr = True

lookupModuleIntf :: ModuleIdent -> FlatState (Maybe CS.Interface)
lookupModuleIntf mid = gets (Map.lookup mid . interfaceEnvE)

getArity :: QualIdent -> FlatState Int
getArity qid = gets (lookupA . typeEnvE)
  where
  lookupA tyEnv = case qualLookupValue qid tyEnv of
    [DataConstructor  _ a _ _] -> a
    [NewtypeConstructor _ _ _] -> 1
    [Value              _ a _] -> a
    [Label              _ _ _] -> 1
    _                          -> case lookupValue (unqualify qid) tyEnv of
      [DataConstructor  _ a _ _] -> a
      [NewtypeConstructor _ _ _] -> 1
      [Value              _ a _] -> a
      [Label              _ _ _] -> 1
      _                          -> internalError $ "GenFlatCurry.getArity: " ++ show qid

ttrans :: Type -> IL.Type
ttrans (TypeVariable          v) = IL.TypeVariable v
ttrans (TypeConstructor    i ts) = IL.TypeConstructor i (map ttrans ts)
ttrans (TypeArrow           f x) = IL.TypeArrow (ttrans f) (ttrans x)
ttrans (TypeConstrained    [] v) = IL.TypeVariable v
ttrans (TypeConstrained (v:_) _) = ttrans v
ttrans (TypeSkolem            k) = internalError $
  "Generators.GenFlatCurry.ttrans: skolem type " ++ show k

-- Constructor (:) receives special treatment throughout the
-- whole implementation. We won't depart from that for mere
-- aesthetic reasons. (hsi)
lookupIdType :: QualIdent -> FlatState (Maybe TypeExpr)
lookupIdType (QualIdent Nothing (Ident _ "[]" _))
  = return (Just l0)
  where l0 = TCons (mkQName ("Prelude", "[]")) [TVar 0]
lookupIdType (QualIdent Nothing (Ident _ ":" _))
  = return (Just (FuncType (TVar 0) (FuncType (l0) (l0))))
  where l0 = TCons (mkQName ("Prelude", "[]")) [TVar 0]
lookupIdType (QualIdent Nothing (Ident _ "()" _))
  = return (Just l0)
  where l0 = TCons (mkQName ("Prelude", "()")) []
lookupIdType (QualIdent Nothing (Ident _ t@('(':',':r) _))
  = return $ Just funtype
  where tupArity   = length r + 1
        argTypes   = map TVar [1 .. tupArity]
        contype    = TCons (mkQName ("Prelude", t)) argTypes
        funtype    = foldr FuncType contype argTypes
lookupIdType qid = do
  aEnv <- gets typeEnvE
  lt <- gets localTypes
  ct <- gets consTypes
  case Map.lookup qid lt `mplus` Map.lookup qid ct of
    Just t  -> Just <$> trType t  -- local name or constructor
    Nothing -> case [ t | Value _ _ (ForAll _ t) <- qualLookupValue qid aEnv ] of
      t : _ -> Just <$> trType (transType t)  -- imported name
      []    -> case qidModule qid of
        Nothing -> return Nothing  -- no known type
        Just _ -> lookupIdType qid {qidModule = Nothing}

-- Generates a new index for a variable
newVarIndex :: Ident -> FlatState VarIndex
newVarIndex ident = do
  idx <- (+1) <$> gets varIndexE
  ty  <- getTypeOf ident
  let vid = VarIndex ty idx
  modify $ \ s -> s { varIndexE = idx, varIdsE = SE.insert ident vid (varIdsE s) }
  return vid

getTypeOf :: Ident -> FlatState (Maybe TypeExpr)
getTypeOf ident = do
  valEnv <- gets typeEnvE
  case lookupValue ident valEnv of
    Value _ _ (ForAll _ t) : _ -> do
      t1 <- trType (ttrans t)
      return (Just t1)
    DataConstructor _ _ _ (ForAllExist _ _ t) : _ -> do
      t1 <- trType (ttrans t)
      return (Just t1)
    _ -> return Nothing

lookupVarIndex :: Ident -> FlatState VarIndex
lookupVarIndex ident = do
  index_ <- gets (SE.lookup ident . varIdsE)
  maybe (internalError $ "GenFlatCurry: missing index for \"" ++ show ident ++ "\"") return index_

clearVarIndices :: FlatState ()
clearVarIndices = modify $ \ s -> s { varIndexE = 0, varIdsE = SE.new }

inNewScope :: FlatState a -> FlatState a
inNewScope act = do
  modify $ \ s -> s { varIdsE = SE.beginScope $ varIdsE s }
  res <- act
  modify $ \ s -> s { varIdsE = SE.endScope $ varIdsE s }
  return res

whenFlatCurry :: FlatState a -> FlatState a -> FlatState a
whenFlatCurry genFlat genIntf
  = gets genInterfaceE >>= (\intf -> if intf then genIntf else genFlat)

-------------------------------------------------------------------------------

-- Generates an evironment containing all public identifiers from the module
-- Note: Currently the record functions (selection and update) for all public
-- record labels are inserted into the environment, though they are not
-- explicitly declared in the export specifications.
genPubEnv :: ModuleIdent -> [CS.IDecl] -> Map.Map Ident IdentExport
genPubEnv mid idecls = foldl (bindEnvIDecl mid) Map.empty idecls

bindIdentExport :: Ident -> Bool -> Map.Map Ident IdentExport -> Map.Map Ident IdentExport
bindIdentExport ident isConstr env =
  maybe (Map.insert ident (if isConstr then OnlyConstr else NotConstr) env)
        (\ ie -> Map.insert ident (updateIdentExport ie isConstr) env)
        (Map.lookup ident env)
  where
  updateIdentExport OnlyConstr    True   = OnlyConstr
  updateIdentExport OnlyConstr    False  = NotOnlyConstr
  updateIdentExport NotConstr     True   = NotOnlyConstr
  updateIdentExport NotConstr     False  = NotConstr
  updateIdentExport NotOnlyConstr _      = NotOnlyConstr

bindEnvIDecl :: ModuleIdent -> Map.Map Ident IdentExport -> CS.IDecl -> Map.Map Ident IdentExport
bindEnvIDecl mid env (CS.IDataDecl _ qid _ cdecls hs)
  = maybe env
    (\ident -> let env'  = bindIdentExport ident False env
                   env'' = foldl bindEnvConstrDecl env'
                     [c | c <- cdecls, CS.constrId c `notElem` hs]
               in foldl bindEnvLabel env'' [l | l <- labels, l `notElem` hs])
    (localIdent mid qid)
  where
    labels = nub $ concatMap CS.recordLabels cdecls
bindEnvIDecl mid env (CS.INewtypeDecl _ qid _ ncdecl hs)
  = maybe env
    (\ident -> let env'  = bindIdentExport ident False env
                   env'' = if ncId `notElem` hs
                              then bindEnvNewConstrDecl env' ncdecl
                              else env'
               in foldl bindEnvLabel env'' [l | l <- labels, l `notElem` hs])
    (localIdent mid qid)
  where
    ncId   = CS.nconstrId ncdecl
    labels = CS.nrecordLabels ncdecl
bindEnvIDecl mid env (CS.ITypeDecl _ qid _ _)
  = maybe env (\ident -> bindIdentExport ident False env) (localIdent mid qid)
bindEnvIDecl mid env (CS.IFunctionDecl _ qid _ _)
  = maybe env (\ident -> bindIdentExport ident False env) (localIdent mid qid)
bindEnvIDecl _ env _ = env

bindEnvConstrDecl :: Map.Map Ident IdentExport -> CS.ConstrDecl -> Map.Map Ident IdentExport
bindEnvConstrDecl env (CS.ConstrDecl  _ _ ident _) = bindIdentExport ident True env
bindEnvConstrDecl env (CS.ConOpDecl _ _ _ ident _) = bindIdentExport ident True env
bindEnvConstrDecl env (CS.RecordDecl  _ _ ident _) = bindIdentExport ident True env

bindEnvLabel :: Map.Map Ident IdentExport -> Ident -> Map.Map Ident IdentExport
bindEnvLabel env l = bindIdentExport l False env

bindEnvNewConstrDecl :: Map.Map Ident IdentExport -> CS.NewConstrDecl -> Map.Map Ident IdentExport
bindEnvNewConstrDecl env (CS.NewConstrDecl _ _ ident _) = bindIdentExport ident False env
bindEnvNewConstrDecl env (CS.NewRecordDecl _ _ ident _) = bindIdentExport ident False env
