-- ---------------------------------------------------------------------------
--
-- GenFlatCurry - Generates FlatCurry program terms and FlatCurry interfaces
--                (type 'FlatCurry.Prog')
--
-- November 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
-- ---------------------------------------------------------------------------
module Generators.GenFlatCurry (genFlatCurry, genFlatInterface) where

-- Haskell libraries
import           Control.Monad       (filterM, liftM, liftM2, liftM3, mplus)
import           Control.Monad.State (State, evalState, gets, modify)
import           Data.List           (mapAccumL, nub)
import qualified Data.Map as Map     (Map, empty, insert, lookup, fromList, toList)
import           Data.Maybe          (catMaybes, fromMaybe, isJust)

-- curry-base
import Curry.Base.Ident as Id

import Curry.ExtendedFlat.Type
import qualified Curry.Syntax as CS

-- Base
import Base.CurryTypes
import Base.Messages (internalError)
import Base.ScopeEnv (ScopeEnv)
import qualified Base.ScopeEnv as ScopeEnv
  (new, insert, lookup, beginScope, endScope)
import Base.TopEnv (topEnvMap)
import Base.Types

 -- environments
import Env.Interface
import Env.TypeConstructor (TCEnv, TypeInfo (..), qualLookupTC)
import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

-- other
import qualified IL as IL
import qualified ModuleSummary
import Transformations (transType)

trace' :: String -> a -> a
trace' _ x = x

-------------------------------------------------------------------------------

-- transforms intermediate language code (IL) to FlatCurry code
genFlatCurry :: ModuleSummary.ModuleSummary -> InterfaceEnv
             -> ValueEnv -> TCEnv -> IL.Module -> Prog
genFlatCurry modSum mEnv tyEnv tcEnv mdl = patchPrelude $
  run modSum mEnv tyEnv tcEnv False (visitModule mdl)

-- transforms intermediate language code (IL) to FlatCurry interfaces
genFlatInterface :: ModuleSummary.ModuleSummary -> InterfaceEnv
                 -> ValueEnv -> TCEnv -> IL.Module -> Prog
genFlatInterface modSum mEnv tyEnv tcEnv mdl = patchPrelude $
  run modSum mEnv tyEnv tcEnv True (visitModule mdl)

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
  , functionIdE   :: (QualIdent, [(Ident, IL.Type)])
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
  , tvarIndexE    :: Int
  , genInterfaceE :: Bool
  , localTypes    :: Map.Map QualIdent IL.Type
  , constrTypes   :: Map.Map QualIdent IL.Type
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
    , functionIdE   = (qualify (mkIdent ""), [])
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
    , varIdsE       = ScopeEnv.new
    , tvarIndexE    = 0
    , genInterfaceE = genIntf
    , localTypes    = Map.empty
    , constrTypes   = Map.fromList $ getConstrTypes tcEnv tyEnv
    }

getConstrTypes :: TCEnv -> ValueEnv -> [(QualIdent, IL.Type)]
getConstrTypes tcEnv tyEnv =
  [ mkConstrType tqid conid argtys argc
  | (_, (_, DataType tqid argc dts):_) <- Map.toList $ topEnvMap tcEnv
  , Just (DataConstr conid _ argtys) <- dts
  ]
  where
  mkConstrType tqid conid argtypes targnum = (conname, contype)
    where
    conname    = QualIdent (qidModule tqid) conid
    resulttype = IL.TypeConstructor tqid (map IL.TypeVariable [0 .. targnum - 1])
    contype    = foldr IL.TypeArrow resulttype $ map (ttrans tcEnv tyEnv) argtypes

--
visitModule :: IL.Module -> FlatState Prog
visitModule (IL.Module mid imps decls) = do
  -- insert local decls into localDecls
  let ts = [ (qn, t) | IL.FunctionDecl qn _ t _ <- decls ]
  modify $ \ s -> s { localTypes = Map.fromList ts }
  ops     <- genOpDecls
  whenFlatCurry
    ( do
      datas   <- mapM visitDataDecl (filter isDataDecl decls)
      types   <- genTypeSynonyms
      recrds  <- genRecordTypes
      funcs   <- mapM visitFuncDecl (filter isFuncDecl decls)
      modid   <- visitModuleIdent mid
      imps'   <- imports
      is      <- mapM visitModuleIdent $ nub $ imps ++ (map extractMid imps')
      return $ Prog modid is (recrds ++ types ++ datas) funcs ops
    )
    ( do
      ds      <- filterM isPublicDataDecl decls
      datas   <- mapM visitDataDecl ds
      types   <- genTypeSynonyms
      recrds  <- genRecordTypes
      fs      <- filterM isPublicFuncDecl decls
      funcs   <- mapM visitFuncDecl fs
      expimps <- getExportedImports
      itypes  <- mapM visitTypeIDecl (filter isTypeIDecl expimps)
      ifuncs  <- mapM visitFuncIDecl (filter isFuncIDecl expimps)
      iops    <- mapM visitOpIDecl (filter isOpIDecl expimps)
      modid   <- visitModuleIdent mid
      imps'   <- imports
      is      <- mapM visitModuleIdent $ nub $ imps ++ (map extractMid imps')
      return $ Prog modid is (itypes ++ recrds ++ types ++ datas) (ifuncs ++ funcs) (iops ++ ops)
    )
  where extractMid (CS.IImportDecl _ mid1) = mid1

--
visitDataDecl :: IL.Decl -> FlatState TypeDecl
visitDataDecl (IL.DataDecl qident arity constrs) = do
  cdecls <- mapM visitConstrDecl constrs
  qname  <- visitQualTypeIdent qident
  vis    <- getVisibility False qident
  return $ Type qname vis [0 .. arity - 1] (concat cdecls)
visitDataDecl _ = internalError "GenFlatCurry: no data declaration"

--
visitConstrDecl :: IL.ConstrDecl [IL.Type] -> FlatState [ConsDecl]
visitConstrDecl (IL.ConstrDecl qident types) = do
  texprs  <- mapM visitType types
  qname   <- visitQualIdent qident
  vis     <- getVisibility True qident
  genFint <- genInterface
  return $ if genFint && vis == Private
    then []
    else [Cons qname (length types) vis texprs]

--
visitType :: IL.Type -> FlatState TypeExpr
visitType (IL.TypeConstructor qid tys) = do
  tys' <- mapM visitType tys
  qn   <- visitQualTypeIdent qid
  return $ if qualName qid == "Identity"
    then head tys'
    else TCons qn tys'
visitType (IL.TypeVariable        idx) = return $ TVar $ abs idx
visitType (IL.TypeArrow       ty1 ty2) = liftM2 FuncType
                                         (visitType ty1) (visitType ty2)

--
visitFuncDecl :: IL.Decl -> FlatState FuncDecl
visitFuncDecl (IL.FunctionDecl qident params typeexpr expression) = do
  let argtypes = splitoffArgTypes typeexpr params
  setFunctionId (qident, argtypes)
  qname <- visitQualIdent qident
  arity <- fromMaybe (length params) `liftM` lookupIdArity qident
  whenFlatCurry
    (do is    <- mapM newVarIndex params
        texpr <- visitType typeexpr
        expr  <- visitExpression expression
        vis   <- getVisibility False qident
        clearVarIndices
        return (Func qname arity vis texpr (Rule is expr))
    )
    (do texpr <- visitType typeexpr
        clearVarIndices
        return (Func qname arity Public texpr (Rule [] (Var $ mkIdx 0)))
    )
visitFuncDecl (IL.ExternalDecl qident _ extname typeexpr) = do
  setFunctionId (qident, [])
  texpr <- visitType typeexpr
  qname <- visitQualIdent qident
  arity <- fromMaybe (typeArity typeexpr) `liftM` lookupIdArity qident
  vis   <- getVisibility False qident
  xname <- visitExternalName extname
  return $ Func qname arity vis texpr (External xname)
visitFuncDecl (IL.NewtypeDecl _ _ _) = do
  mid <- moduleId
  internalError $ "\"" ++ Id.moduleName mid
    ++ "\": newtype declarations are not supported"
visitFuncDecl _ = internalError "GenFlatCurry: no function declaration"

--
visitExpression :: IL.Expression -> FlatState Expr
visitExpression (IL.Literal       l) = Lit `liftM` visitLiteral l
visitExpression (IL.Variable      v) = Var `liftM` lookupVarIndex v
visitExpression (IL.Function    f _) = do
  arity_ <- lookupIdArity f
  qname <- visitQualIdent f
  case arity_ of
    Nothing -> internalError $ funcArity qname
    Just a  -> genFuncCall qname a []
visitExpression (IL.Constructor c _) = do
  arity_ <- lookupIdArity c
  qname <- visitQualIdent c
  case arity_ of
    Nothing -> internalError $ consArity qname
    Just a  -> genConsCall qname a []
visitExpression (IL.Apply     e1 e2) = genFlatApplication e1 e2
visitExpression (IL.Case  r ea e bs) =
  liftM3 (Case r) (visitEval ea) (visitExpression e) (mapM visitAlt bs)
visitExpression (IL.Or        e1 e2) = do
  e1' <- visitExpression e1
  e2' <- visitExpression e2
--   checkOverlapping e1' e2'
  return $ Or e1' e2'
visitExpression (IL.Exist       v e) = do
  idx <- newVarIndex v
  e'  <- visitExpression e
  return $ case e' of
    Free is e'' -> Free (idx : is) e''
    _           -> Free [idx] e'
visitExpression (IL.Let        bd e) = inNewScope $ do
  _ <- newVarIndex $ bindingIdent bd
  bind <- visitBinding bd
  e' <- visitExpression e
  return $ case e' of -- TODO bjp(2011-09-21): maybe remove again
    (Let binds e'') -> Let (bind:binds) e''
    _               -> Let [bind] e'
  -- is it correct that there is no endScope? (hsi): bjp: Just added, but no reasoning about
visitExpression (IL.Letrec    bds e) = inNewScope $ do
  mapM_ (newVarIndex . bindingIdent) bds
  bds' <- mapM visitBinding bds
  e' <- visitExpression e
  return $ Let bds' e'
visitExpression (IL.Typed e ty) = liftM2 Typed (visitExpression e)
                                               (visitType ty)

--
visitLiteral :: IL.Literal -> FlatState Literal
visitLiteral (IL.Char  rs c) = return $ Charc  rs c
visitLiteral (IL.Int   rs i) = return $ Intc   rs i
visitLiteral (IL.Float rs f) = return $ Floatc rs f

--
visitAlt :: IL.Alt -> FlatState BranchExpr
visitAlt (IL.Alt p e) = liftM2 Branch (visitConstrTerm p) (visitExpression e)

--
visitConstrTerm :: IL.ConstrTerm -> FlatState Pattern
visitConstrTerm (IL.LiteralPattern        l) = LPattern `liftM` visitLiteral l
visitConstrTerm (IL.ConstructorPattern c vs) =
  liftM2 (flip Pattern) (mapM newVarIndex vs) (visitQualIdent c) -- TODO: is this flip needed?
visitConstrTerm (IL.VariablePattern       _) = do
  mid <- moduleId
  internalError $ "\"" ++ Id.moduleName mid ++ "\": variable patterns are not supported"

--
visitEval :: IL.Eval -> FlatState CaseType
visitEval IL.Rigid = return Rigid
visitEval IL.Flex  = return Flex

--
visitBinding :: IL.Binding -> FlatState (VarIndex, Expr)
visitBinding (IL.Binding v e) = liftM2 (,) (lookupVarIndex v) (visitExpression e)

-------------------------------------------------------------------------------

--
visitFuncIDecl :: CS.IDecl -> FlatState FuncDecl
visitFuncIDecl (CS.IFunctionDecl _ f a ty) = do
  texpr <- visitType $ snd $ cs2ilType [] ty
  qname <- visitQualIdent f
  return $ Func qname a Public texpr (Rule [] (Var $ mkIdx 0))
visitFuncIDecl _ = internalError "GenFlatCurry: no function interface"

--
visitTypeIDecl :: CS.IDecl -> FlatState TypeDecl
visitTypeIDecl (CS.IDataDecl _ t vs cs) = do
  let mid = fromMaybe (internalError "GenFlatCurry: no module name") (qidModule t)
      is  = [0 .. length vs - 1]
  cdecls <- mapM (visitConstrIDecl mid $ zip vs is) $ catMaybes cs
  qname  <- visitQualTypeIdent t
  return $ Type qname Public is cdecls
visitTypeIDecl (CS.ITypeDecl _ t vs ty) = do
  let is = [0 .. length vs - 1]
  ty'   <- visitType $ snd $ cs2ilType (zip vs is) ty
  qname <- visitQualTypeIdent t
  return $ TypeSyn qname Public is ty'
visitTypeIDecl _ = internalError "GenFlatCurry: no type interface"

--
visitConstrIDecl :: ModuleIdent -> [(Ident, Int)] -> CS.ConstrDecl
                 -> FlatState ConsDecl
visitConstrIDecl mid tis (CS.ConstrDecl _ _ ident typeexprs) = do
  texprs <- mapM (visitType . (snd . cs2ilType tis)) typeexprs
  qname  <- visitQualIdent (qualifyWith mid ident)
  return (Cons qname (length typeexprs) Public texprs)
visitConstrIDecl mid tis (CS.ConOpDecl pos ids type1 ident type2)
  = visitConstrIDecl mid tis (CS.ConstrDecl pos ids ident [type1,type2])

--
visitOpIDecl :: CS.IDecl -> FlatState OpDecl
visitOpIDecl (CS.IInfixDecl _ fixi prec op) = do
  op' <- visitQualIdent op
  return $ Op op' (genFixity fixi) prec
visitOpIDecl _ = internalError "GenFlatCurry.visitOpIDecl: no pattern match"

-------------------------------------------------------------------------------

--
visitModuleIdent :: ModuleIdent -> FlatState String
visitModuleIdent = return . Id.moduleName

--
visitQualIdent :: QualIdent -> FlatState QName
visitQualIdent qident = do
  mid <- moduleId
  let (mmod, ident) = (qidModule qident, qidIdent qident)
      modid | elem ident [listId, consId, nilId, unitId] || isTupleId ident
            = Id.moduleName preludeMIdent
            | otherwise
            = maybe (Id.moduleName mid) Id.moduleName mmod
  ftype <- lookupIdType qident
  return (QName Nothing ftype modid $ idName ident)

-- This variant of visitQualIdent does not look up the type of the identifier,
-- which is wise when the identifier is bound to a type, because looking up
-- the type of a type via lookupIdType will get stuck in an endless loop. (hsi)
visitQualTypeIdent :: QualIdent -> FlatState QName
visitQualTypeIdent qident = do
  mid <- moduleId
  let (mmod, ident) = (qidModule qident, qidIdent qident)
      modid | elem ident [listId, consId, nilId, unitId] || isTupleId ident
            = Id.moduleName preludeMIdent
            | otherwise
            = maybe (Id.moduleName mid) Id.moduleName mmod
  return (QName Nothing Nothing modid $ idName ident)

--
visitExternalName :: String -> FlatState String
visitExternalName extname
  = moduleId >>= \mid -> return (Id.moduleName mid ++ "." ++ extname)


-------------------------------------------------------------------------------

--
getVisibility :: Bool -> QualIdent -> FlatState Visibility
getVisibility isConstr qident = do
  public <- isPublic isConstr qident
  return $ if public then Public else Private

--
getExportedImports :: FlatState [CS.IDecl]
getExportedImports = do
  mid  <- moduleId
  exps <- exports
  genExportedIDecls $ Map.toList $ getExpImports mid Map.empty exps

--
getExpImports :: ModuleIdent -> Map.Map ModuleIdent [CS.Export] -> [CS.Export]
		 -> Map.Map ModuleIdent [CS.Export]
getExpImports _      expenv [] = expenv
getExpImports mident expenv ((CS.Export qident):exps)
  = getExpImports mident
    (bindExpImport mident qident (CS.Export qident) expenv)
    exps
getExpImports mident expenv ((CS.ExportTypeWith qident idents):exps)
  = getExpImports mident
    (bindExpImport mident qident (CS.ExportTypeWith qident idents) expenv)
    exps
getExpImports mident expenv ((CS.ExportTypeAll qident):exps)
  = getExpImports mident
    (bindExpImport mident qident (CS.ExportTypeAll qident) expenv)
    exps
getExpImports mident expenv ((CS.ExportModule mident'):exps)
  = getExpImports mident (Map.insert mident' [] expenv) exps

--
bindExpImport :: ModuleIdent -> QualIdent -> CS.Export
	         -> Map.Map ModuleIdent [CS.Export] -> Map.Map ModuleIdent [CS.Export]
bindExpImport mident qident export expenv
  | isJust (localIdent mident qident)
  = expenv
  | otherwise
  = let (Just modid) = qidModule qident
    in  maybe (Map.insert modid [export] expenv)
              (\es -> Map.insert modid (export:es) expenv)
              (Map.lookup modid expenv)

--
genExportedIDecls :: [(ModuleIdent,[CS.Export])] -> FlatState [CS.IDecl]
genExportedIDecls mes = genExpIDecls [] mes

--
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

--
isExportedIDecl :: [CS.Export] -> CS.IDecl -> Bool
isExportedIDecl exprts (CS.IInfixDecl _ _ _ qident)
  = isExportedQualIdent qident exprts
isExportedIDecl exprts (CS.IDataDecl _ qident _ _)
  = isExportedQualIdent qident exprts
isExportedIDecl exprts (CS.ITypeDecl _ qident _ _)
  = isExportedQualIdent qident exprts
isExportedIDecl exprts (CS.IFunctionDecl _ qident _ _)
  = isExportedQualIdent qident exprts
isExportedIDecl _ _ = False

--
isExportedQualIdent :: QualIdent -> [CS.Export] -> Bool
isExportedQualIdent _ [] = False
isExportedQualIdent qident ((CS.Export qident'):exps)
  = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((CS.ExportTypeWith qident' _):exps)
  = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((CS.ExportTypeAll qident'):exps)
  = qident == qident' || isExportedQualIdent qident exps
isExportedQualIdent qident ((CS.ExportModule _):exps)
  = isExportedQualIdent qident exps

--
qualifyIDecl :: ModuleIdent -> CS.IDecl -> CS.IDecl
qualifyIDecl mid (CS.IInfixDecl   pos fixi prec qid)
  = CS.IInfixDecl pos fixi prec (qualQualify mid qid)
qualifyIDecl mid (CS.IDataDecl    pos qid vs cs)
  = CS.IDataDecl pos (qualQualify mid qid) vs
  $ map (fmap (qualifyIConstrDecl mid)) cs
qualifyIDecl mid (CS.INewtypeDecl  pos qid vs nc)
  = CS.INewtypeDecl pos (qualQualify mid qid) vs nc
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

qualifyCSType :: ModuleIdent -> CS.TypeExpr -> CS.TypeExpr
qualifyCSType mid = fromType . toQualType mid []


--
typeArity :: IL.Type -> Int
typeArity (IL.TypeArrow _ t)       = 1 + (typeArity t)
typeArity (IL.TypeConstructor _ _) = 0
typeArity (IL.TypeVariable _)      = 0


-------------------------------------------------------------------------------

--
genFlatApplication :: IL.Expression -> IL.Expression -> FlatState Expr
genFlatApplication e1 e2 = genFlatApplic [e2] e1
  where
  genFlatApplic args expression = case expression of
    (IL.Apply expr1 expr2) -> genFlatApplic (expr2:args) expr1
    (IL.Function qident _) -> do
      arity_ <- lookupIdArity qident
      qname <- visitQualIdent qident
      maybe (internalError (funcArity qident))
            (\arity -> genFuncCall qname arity args)
            arity_
    (IL.Constructor qident _) -> do
      arity_ <- lookupIdArity qident
      qname <- visitQualIdent qident
      maybe (internalError (consArity qident))
            (\arity -> genConsCall qname arity args)
            arity_
    _ -> do
      expr <- visitExpression expression
      genApplicComb expr args

--
genFuncCall :: QName -> Int -> [IL.Expression] -> FlatState Expr
genFuncCall qname arity args
  | arity > cnt = genComb qname args $ FuncPartCall $ arity - cnt
  | arity < cnt = do
      let (funcargs, applicargs) = splitAt arity args
      funccall <- genComb qname funcargs FuncCall
      genApplicComb funccall applicargs
   | otherwise  = genComb qname args FuncCall
 where cnt = length args

--
genConsCall :: QName -> Int -> [IL.Expression] -> FlatState Expr
genConsCall qname arity args
   | arity > cnt
     = genComb qname args (ConsPartCall (arity - cnt))
   | arity < cnt
     = do let (funcargs, applicargs) = splitAt arity args
	  conscall <- genComb qname funcargs ConsCall
	  genApplicComb conscall applicargs
   | otherwise
     = genComb qname args ConsCall
 where cnt = length args

--
genComb :: QName -> [IL.Expression] -> CombType -> FlatState Expr
genComb qname args combtype
   = do exprs <- mapM visitExpression args
	return (Comb combtype qname exprs)

--
genApplicComb :: Expr -> [IL.Expression] -> FlatState Expr
genApplicComb expr [] = return expr
genApplicComb expr (e1:es) = do
  expr1 <- visitExpression e1
  qname <- visitQualIdent qidApply
  genApplicComb (Comb FuncCall qname [expr, expr1]) es
  where
  qidApply = qualifyWith preludeMIdent (mkIdent "apply")

--
genOpDecls :: FlatState [OpDecl]
genOpDecls = fixities >>= mapM genOpDecl

--
genOpDecl :: CS.IDecl -> FlatState OpDecl
genOpDecl (CS.IInfixDecl _ fix prec qident) = do
  qname <- visitQualIdent qident
  return $ Op qname (genFixity fix) prec
genOpDecl _ = internalError "GenFlatCurry: no infix interface"

genFixity :: CS.Infix -> Fixity
genFixity CS.InfixL = InfixlOp
genFixity CS.InfixR = InfixrOp
genFixity CS.Infix  = InfixOp

-- The intermediate language (IL) does not represent type synonyms
-- (and also no record declarations). For this reason an interface
-- representation of all type synonyms is generated (see "ModuleSummary")
-- from the abstract syntax representation of the Curry program.
-- The function 'typeSynonyms' returns this list of type synonyms.
genTypeSynonyms ::  FlatState [TypeDecl]
genTypeSynonyms = typeSynonyms >>= mapM genTypeSynonym

--
genTypeSynonym :: CS.IDecl -> FlatState TypeDecl
genTypeSynonym (CS.ITypeDecl _ qident params ty) = do
  let is = [0 .. (length params) - 1]
  tyEnv <- gets typeEnvE
  tcEnv <- gets tConsEnvE
  let ty' = elimRecordTypes tyEnv tcEnv ty
  texpr <- visitType $ snd $ cs2ilType (zip params is) ty'
  qname <- visitQualTypeIdent qident
  vis   <- getVisibility False qident
  return $ TypeSyn qname vis is texpr
genTypeSynonym _ = internalError "GenFlatCurry: no type synonym interface"

-- In order to provide an interface for record declarations, 'genRecordTypes'
-- generates dummy data declarations representing records together
-- with their typed labels. For the record declaration
--
--      type Rec = {l_1 :: t_1,..., l_n :: t_n}
--
-- the following data declaration will be generated:
--
--      data Rec' = l_1' t_1 | ... | l_n' t_n
--
-- Rec' and l_i' are unique idenfifiers which encode the original names
-- Rec and l_i.
-- When reading an interface file containing such declarations, it is
-- now possible to reconstruct the original record declaration. Since
-- usual FlatCurry code is used, these declaration should not have any
-- effects on the behaviour of the Curry program. But to ensure correctness,
-- these dummies should be generated for the interface file as well as for
-- the corresponding FlatCurry file.
genRecordTypes :: FlatState [TypeDecl]
genRecordTypes = records >>= mapM genRecordType

--
genRecordType :: CS.IDecl -> FlatState TypeDecl
genRecordType (CS.ITypeDecl _ qid params (CS.RecordType fs)) = do
  let is = [0 .. (length params) - 1]
      (mid, ident) = (qidModule qid, qidIdent qid)
  qname <- visitQualIdent ((maybe qualify qualifyWith mid) (recordExtId ident))
  labels <- mapM (genRecordLabel mid (zip params is)) fs
  return (Type qname Public is labels)
genRecordType _ = internalError "GenFlatCurry.genRecordType: no pattern match"

--
genRecordLabel :: Maybe ModuleIdent -> [(Ident, Int)] -> ([Ident], CS.TypeExpr)
               -> FlatState ConsDecl
genRecordLabel modid vis ([ident],ty) = do
  tyEnv <- gets typeEnvE
  tcEnv <- gets tConsEnvE
  let ty' = elimRecordTypes tyEnv tcEnv ty
  texpr <- visitType (snd (cs2ilType vis ty'))
  qname <- visitQualIdent ((maybe qualify qualifyWith modid)
                            (labelExtId ident))
  return (Cons qname 1 Public [texpr])
genRecordLabel _ _ _ = internalError "GenFlatCurry.genRecordLabel: no pattern match"


-------------------------------------------------------------------------------

-- FlatCurry provides no possibility of representing record types like
-- {l_1::t_1, l_2::t_2, ..., l_n::t_n}. So they have to be transformed to
-- to the corresponding type constructors which are defined in the record
-- declarations.
-- Unlike data declarations or function type annotations, type synonyms and
-- record declarations are not generated from the intermediate language.
-- So the transformation has only to be performed in these cases.
elimRecordTypes :: ValueEnv -> TCEnv -> CS.TypeExpr -> CS.TypeExpr
elimRecordTypes tyEnv tcEnv (CS.ConstructorType qid tys)
   = CS.ConstructorType qid (map (elimRecordTypes tyEnv tcEnv) tys)
elimRecordTypes _ _ (CS.VariableType ident)
   = CS.VariableType ident
elimRecordTypes tyEnv tcEnv (CS.TupleType tys)
   = CS.TupleType (map (elimRecordTypes tyEnv tcEnv) tys)
elimRecordTypes tyEnv tcEnv (CS.ListType ty)
   = CS.ListType (elimRecordTypes tyEnv tcEnv ty)
elimRecordTypes tyEnv tcEnv (CS.ArrowType ty1 ty2)
   = CS.ArrowType (elimRecordTypes tyEnv tcEnv ty1)
                  (elimRecordTypes tyEnv tcEnv ty2)
elimRecordTypes tyEnv tcEnv (CS.RecordType fss)
   = let fs = flattenRecordTypeFields fss
     in  case (lookupValue (fst (head fs)) tyEnv) of
          [Label _ record _] ->
            case (qualLookupTC record tcEnv) of
              [AliasType _ n (TypeRecord fs')] ->
                let ms = foldl (matchTypeVars fs) Map.empty fs'
                    types = map (\i -> maybe
                                        (CS.VariableType
                                            (mkIdent ("#tvar" ++ show i)))
                                        (elimRecordTypes tyEnv tcEnv)
                                        (Map.lookup i ms))
                                [0 .. n-1]
                in  CS.ConstructorType record types
              _ -> internalError ("GenFlatCurry.elimRecordTypes: "
                                  ++ "no record type")
          _ -> internalError ("GenFlatCurry.elimRecordTypes: "
                              ++ "no label")

matchTypeVars :: [(Ident,CS.TypeExpr)] -> Map.Map Int CS.TypeExpr
	      -> (Ident, Type) -> Map.Map Int CS.TypeExpr
matchTypeVars fs ms (l,ty) = maybe ms (match ms ty) (lookup l fs)
  where
  match ms1 (TypeVariable i) typeexpr = Map.insert i typeexpr ms1
  match ms1 (TypeConstructor _ tys) (CS.ConstructorType _ typeexprs)
     = matchList ms1 tys typeexprs
  match ms1 (TypeConstructor _ tys) (CS.ListType typeexpr)
     = matchList ms1 tys [typeexpr]
  match ms1 (TypeConstructor _ tys) (CS.TupleType typeexprs)
     = matchList ms1 tys typeexprs
  match ms1 (TypeArrow ty1 ty2) (CS.ArrowType typeexpr1 typeexpr2)
     = matchList ms1 [ty1,ty2] [typeexpr1,typeexpr2]
  match ms1 (TypeRecord fs') (CS.RecordType fss)
     = foldl (matchTypeVars (flattenRecordTypeFields fss)) ms1 fs'
  match _ ty1 typeexpr
     = internalError ("GenFlatCurry.matchTypeVars: "
                      ++ show ty1 ++ "\n" ++ show typeexpr)

  matchList ms1 tys
     = foldl (\ms' (ty',typeexpr) -> match ms' ty' typeexpr) ms1 . zip tys

flattenRecordTypeFields :: [([Ident], CS.TypeExpr)] -> [(Ident, CS.TypeExpr)]
flattenRecordTypeFields = concatMap (\ (ls, ty) -> map (\l -> (l, ty)) ls)

cs2ilType :: [(Ident,Int)] -> CS.TypeExpr -> ([(Ident,Int)], IL.Type)
cs2ilType ids (CS.ConstructorType qident typeexprs)
  = let (ids', ilTypeexprs) = mapAccumL cs2ilType ids typeexprs
    in  (ids', IL.TypeConstructor qident ilTypeexprs)
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
cs2ilType _ typeexpr = internalError $ "GenFlatCurry.cs2ilType: " ++ show typeexpr

-------------------------------------------------------------------------------
-- Messages for internal errors and warnings
funcArity :: Show a => a -> [Char]
funcArity qid = "GenFlatCurry: missing arity for function \"" ++ show qid ++ "\""

consArity :: Show a => a -> [Char]
consArity qid = "GenFlatCurry: missing arity for constructor \""
  ++ show qid ++ "\""

missingVarIndex :: Show a => a -> [Char]
missingVarIndex ident = "GenFlatCurry: missing index for \"" ++ show ident ++ "\""

-------------------------------------------------------------------------------

--
isDataDecl :: IL.Decl -> Bool
isDataDecl (IL.DataDecl _ _ _) = True
isDataDecl _                   = False

--
isFuncDecl :: IL.Decl -> Bool
isFuncDecl (IL.FunctionDecl _ _ _ _) = True
isFuncDecl (IL.ExternalDecl _ _ _ _) = True
isFuncDecl _                         = False

--
isPublicDataDecl :: IL.Decl -> FlatState Bool
isPublicDataDecl (IL.DataDecl qident _ _) = isPublic False qident
isPublicDataDecl _                        = return False

--
isPublicFuncDecl :: IL.Decl -> FlatState Bool
isPublicFuncDecl (IL.FunctionDecl qident _ _ _) = isPublic False qident
isPublicFuncDecl (IL.ExternalDecl qident _ _ _) = isPublic False qident
isPublicFuncDecl _                              = return False

--
isTypeIDecl :: CS.IDecl -> Bool
isTypeIDecl (CS.IDataDecl _ _ _ _) = True
isTypeIDecl (CS.ITypeDecl _ _ _ _) = True
isTypeIDecl _                      = False

--
isRecordIDecl :: CS.IDecl -> Bool
isRecordIDecl (CS.ITypeDecl _ _ _ (CS.RecordType (_:_))) = True
isRecordIDecl _                                          = False

--
isFuncIDecl :: CS.IDecl -> Bool
isFuncIDecl (CS.IFunctionDecl _ _ _ _) = True
isFuncIDecl _                          = False

--
isOpIDecl :: CS.IDecl -> Bool
isOpIDecl (CS.IInfixDecl _ _ _ _) = True
isOpIDecl _                       = False

--
bindingIdent :: IL.Binding -> Ident
bindingIdent (IL.Binding ident _) = ident

-- ---------------------------------------------------------------------------

--
moduleId :: FlatState ModuleIdent
moduleId = gets moduleIdE

--
setFunctionId :: (QualIdent, [(Ident, IL.Type)]) -> FlatState ()
setFunctionId qid = modify $ \ s -> s { functionIdE = qid }

--
exports :: FlatState [CS.Export]
exports = gets exportsE

--
imports :: FlatState [CS.IImportDecl]
imports = gets importsE

--
records :: FlatState [CS.IDecl]
records = gets (filter isRecordIDecl . interfaceE)

--
fixities :: FlatState [CS.IDecl]
fixities = gets fixitiesE

--
typeSynonyms :: FlatState [CS.IDecl]
typeSynonyms = gets typeSynonymsE

--
isPublic :: Bool -> QualIdent -> FlatState Bool
isPublic isConstr qid = gets $ \ s -> maybe False isP
  (Map.lookup (unqualify qid) $ publicEnvE s)
  where
  isP NotConstr     = not isConstr
  isP OnlyConstr    = isConstr
  isP NotOnlyConstr = True

--
lookupModuleIntf :: ModuleIdent -> FlatState (Maybe CS.Interface)
lookupModuleIntf mid = gets (Map.lookup mid . interfaceEnvE)

--
lookupIdArity :: QualIdent -> FlatState (Maybe Int)
lookupIdArity qid = gets (lookupA . typeEnvE)
  where
  lookupA tyEnv = case qualLookupValue qid tyEnv of
    [DataConstructor  _ a _] -> Just a
    [NewtypeConstructor _ _] -> Just 1
    [Value            _ a _] -> Just a
    []                       -> case lookupValue (unqualify qid) tyEnv of
      [DataConstructor  _ a _] -> Just a
      [NewtypeConstructor _ _] -> Just 1
      [Value            _ a _] -> Just a
      _                        -> Nothing
    _                        -> Nothing

ttrans :: TCEnv -> ValueEnv -> Type -> IL.Type
ttrans _     _     (TypeVariable          v) = IL.TypeVariable v
ttrans tcEnv tyEnv (TypeConstructor    i ts) = IL.TypeConstructor i (map (ttrans tcEnv tyEnv) ts)
ttrans tcEnv tyEnv (TypeArrow           f x) = IL.TypeArrow (ttrans tcEnv tyEnv f) (ttrans tcEnv tyEnv x)
ttrans _     _     (TypeConstrained    [] v) = IL.TypeVariable v
ttrans tcEnv tyEnv (TypeConstrained (v:_) _) = ttrans tcEnv tyEnv v
ttrans _     _     (TypeSkolem            k) = internalError $
  "Generators.GenFlatCurry.ttrans: skolem type " ++ show k
ttrans _     _     (TypeRecord           []) = internalError $
  "Generators.GenFlatCurry.ttrans: empty type record"
ttrans tcEnv tyEnv (TypeRecord   ((l, _):_)) = case lookupValue l tyEnv of
  [Label _ rec _ ] -> case qualLookupTC rec tcEnv of
    [AliasType _ n (TypeRecord _)] ->
      IL.TypeConstructor rec (map IL.TypeVariable [0 .. n - 1])
    _ -> internalError $ "Generators.GenFlatCurry.ttrans: unknown record type " ++ show rec
  _ -> internalError $ "Generators.GenFlatCurry.ttrans: ambigous record label " ++ show l

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
  ct <- gets constrTypes
  m  <- gets moduleIdE
  tyEnv <- gets typeEnvE
  tcEnv <- gets tConsEnvE
  case Map.lookup qid lt `mplus` Map.lookup qid ct of
    Just t  -> trace' ("lookupIdType local " ++ show (qid, t)) $ liftM Just (visitType t)  -- local name or constructor
    Nothing -> case [ t | Value _ _ (ForAll _ t) <- qualLookupValue qid aEnv ] of
      t : _ -> liftM Just (visitType (transType m tyEnv tcEnv t))  -- imported name
      []    -> case qidModule qid of
        Nothing -> trace' ("no type for "  ++ show qid) $ return Nothing  -- no known type
        Just _ -> lookupIdType qid {qidModule = Nothing}
--

-- Generates a new index for a variable
newVarIndex :: Ident -> FlatState VarIndex
newVarIndex ident = do
  idx <- (+1) `liftM` gets varIndexE
  ty  <- getTypeOf ident
  let vid = VarIndex ty idx
  modify $ \ s -> s { varIndexE = idx, varIdsE = ScopeEnv.insert ident vid (varIdsE s) }
  return vid

getTypeOf :: Ident -> FlatState (Maybe TypeExpr)
getTypeOf ident = do
  valEnv <- gets typeEnvE
  tcEnv  <- gets tConsEnvE
  case lookupValue ident valEnv of
    Value _ _ (ForAll _ t) : _ -> do
      t1 <- visitType (ttrans tcEnv valEnv t)
      trace' ("getTypeOf(" ++ show ident ++ ") = " ++ show t1) $
        return (Just t1)
    DataConstructor _ _ (ForAllExist _ _ t) : _ -> do
      t1 <- visitType (ttrans tcEnv valEnv t)
      trace' ("getTypeOfDataCon(" ++ show ident ++ ") = " ++ show t1) $
        return (Just t1)
    _ -> do
    (_, ats) <- gets functionIdE
    case lookup ident ats of
      Just t -> liftM Just (visitType t)
      Nothing -> trace' ("lookupValue did not return a value for index " ++ show ident)
                 (return Nothing)

--
lookupVarIndex :: Ident -> FlatState VarIndex
lookupVarIndex ident = do
  index_ <- gets (ScopeEnv.lookup ident . varIdsE)
  maybe (internalError $ missingVarIndex ident) return index_

--
clearVarIndices :: FlatState ()
clearVarIndices = modify $ \ s -> s { varIndexE = 0, varIdsE = ScopeEnv.new }

--
genInterface :: FlatState Bool
genInterface = gets genInterfaceE

inNewScope :: FlatState a -> FlatState a
inNewScope act = do
  modify $ \ s -> s { varIdsE  = ScopeEnv.beginScope $ varIdsE s }
  res <- act
  modify $ \ s -> s { varIdsE  = ScopeEnv.endScope $ varIdsE s }
  return res

--
whenFlatCurry :: FlatState a -> FlatState a -> FlatState a
whenFlatCurry genFlat genIntf
  = genInterface >>= (\intf -> if intf then genIntf else genFlat)

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

--
bindEnvIDecl :: ModuleIdent -> Map.Map Ident IdentExport -> CS.IDecl -> Map.Map Ident IdentExport
bindEnvIDecl mid env (CS.IDataDecl _ qid _ mcdecls)
  = maybe env
    (\ident -> foldl bindEnvConstrDecl (bindIdentExport ident False env)
            (catMaybes mcdecls))
    (localIdent mid qid)
bindEnvIDecl mid env (CS.INewtypeDecl _ qid _ ncdecl)
  = maybe env
    (\ident -> bindEnvNewConstrDecl (bindIdentExport ident False env) ncdecl)
    (localIdent mid qid)
bindEnvIDecl mid env (CS.ITypeDecl _ qid _ texpr)
  = maybe env (\ident -> bindEnvITypeDecl env ident texpr) (localIdent mid qid)
bindEnvIDecl mid env (CS.IFunctionDecl _ qid _ _)
  = maybe env (\ident -> bindIdentExport ident False env) (localIdent mid qid)
bindEnvIDecl _ env _ = env

--
bindEnvITypeDecl :: Map.Map Ident IdentExport -> Ident -> CS.TypeExpr
                 -> Map.Map Ident IdentExport
bindEnvITypeDecl env ident (CS.RecordType fs)
  = bindIdentExport ident False (foldl (bindEnvRecordLabel ident) env fs)
bindEnvITypeDecl env ident _ = bindIdentExport ident False env

--
bindEnvConstrDecl :: Map.Map Ident IdentExport -> CS.ConstrDecl -> Map.Map Ident IdentExport
bindEnvConstrDecl env (CS.ConstrDecl  _ _ ident _) = bindIdentExport ident True env
bindEnvConstrDecl env (CS.ConOpDecl _ _ _ ident _) = bindIdentExport ident True env

--
bindEnvNewConstrDecl :: Map.Map Ident IdentExport -> CS.NewConstrDecl -> Map.Map Ident IdentExport
bindEnvNewConstrDecl env (CS.NewConstrDecl _ _ ident _) = bindIdentExport ident False env

--
bindEnvRecordLabel :: Ident -> Map.Map Ident IdentExport -> ([Ident],CS.TypeExpr) -> Map.Map Ident IdentExport
bindEnvRecordLabel r env ([lab], _) = bindIdentExport (recSelectorId (qualify r) lab) False expo
  where expo = (bindIdentExport (recUpdateId (qualify r) lab) False env)
bindEnvRecordLabel _ _ _ = internalError "GenFlatCurry.bindEnvRecordLabel: no pattern match"

splitoffArgTypes :: IL.Type -> [Ident] -> [(Ident, IL.Type)]
splitoffArgTypes (IL.TypeArrow l r) (i:is) = (i, l):splitoffArgTypes r is
splitoffArgTypes _ [] = []
splitoffArgTypes _ _  = internalError "splitoffArgTypes"
