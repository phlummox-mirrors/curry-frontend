{- |
    Module      :  $Header$
    Description :  Generation of AbstractCurry program terms
    Copyright   :  (c) 2005, Martin Engelke  (men@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module contains the generation of an 'AbstractCurry' program term
    for a given 'Curry' module.
-}
module Generators.GenAbstractCurry
  ( genTypedAbstract, genUntypedAbstract ) where

import Data.List (find, mapAccumL)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, isJust)
import qualified Data.Set as Set

import Curry.AbstractCurry
import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.CurryTypes (fromType)
import Base.Messages (internalError)
import Base.TopEnv
import Base.Types

import Env.TypeConstructor (TCEnv, lookupTC)
import Env.Value (ValueEnv, ValueInfo (..), lookupValue, qualLookupValue)

import CompilerEnv

-- ---------------------------------------------------------------------------
-- Interface
-- ---------------------------------------------------------------------------

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
genAbstract ty env mdl@(Module mid _ imps decls)
  = CurryProg mid' imps' types funcs ops
  where
  aEnv  = abstractEnv ty env mdl
  mid'  = moduleName mid
  imps' = map genImportDecl imps
  types = snd $ mapAccumL genTypeDecl aEnv         $ reverse $ typeDecls part
  funcs = snd $ mapAccumL (genFuncDecl False) aEnv $ funcDecls part
  ops   =       concatMap (genOpDecl aEnv)         $ reverse $ opDecls part
  part  = foldl partitionDecl emptyPartition decls

-- ---------------------------------------------------------------------------
-- Partition of declarations
-- ---------------------------------------------------------------------------

-- The following code is used to split a list of Curry declarations into
-- three parts:
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
  { typeDecls   :: [Decl]
  , funcDecls   :: [(Ident, [Decl])] -- no Map to preserve order
  , opDecls     :: [Decl]
  } deriving Show

-- |Generate initial partitions
emptyPartition :: Partition
emptyPartition = Partition
  { typeDecls   = []
  , funcDecls   = []
  , opDecls     = []
  }

-- |Insert a CurrySyntax top level declaration into a partition.
-- /Note:/ Declarations are collected in reverse order.
partitionDecl :: Partition -> Decl -> Partition
-- operator infix declarations
partitionDecl p d@(InfixDecl _ _ _ _) = p { opDecls   = d : opDecls   p }
-- type declarations
partitionDecl p d@(DataDecl  _ _ _ _) = p { typeDecls = d : typeDecls p }
partitionDecl p d@(TypeDecl  _ _ _ _) = p { typeDecls = d : typeDecls p }
-- function declarations
partitionDecl p (TypeSig pos ids ty)
  = partitionFuncDecls (\q -> TypeSig pos [q] ty) p ids
partitionDecl p d@(FunctionDecl _ ident _)
  = partitionFuncDecls (const d) p [ident]
partitionDecl p d@(ExternalDecl _ _ _ ident _)
  = partitionFuncDecls (const d) p [ident]
partitionDecl p (FlatExternalDecl pos ids)
  = partitionFuncDecls (\q -> FlatExternalDecl pos [q]) p ids
-- other (ignored)
partitionDecl p _ = p

--
partitionFuncDecls :: (Ident -> Decl) -> Partition -> [Ident] -> Partition
partitionFuncDecls genDecl parts fs
  = parts { funcDecls = foldl insertDecls (funcDecls parts) fs }
  where
  insertDecls funcs f = case span ((/=f) . fst) funcs of
    (others, []                ) -> others ++ (f, genDecl f : []    ) : []
    (others, (_, fDecls) : rest) -> others ++ (f, genDecl f : fDecls) : rest

-- ---------------------------------------------------------------------------
-- Conversion from Curry to AbstractCurry
-- ---------------------------------------------------------------------------

--
genImportDecl :: ImportDecl -> String
genImportDecl (ImportDecl _ mid _ _ _) = moduleName mid

--
genTypeDecl :: AbstractEnv -> Decl -> (AbstractEnv, CTypeDecl)
genTypeDecl env (DataDecl _ n vs cs)
  = ( resetScope env2
    , CType (genQName True env2 $ qualifyWith (moduleId env) n)
            (genVisibility env2 n)
            (zip idxs $ map idName vs)
            cs'
    )
  where (env1, idxs) = mapAccumL genTVarIndex env vs
        (env2, cs' ) = mapAccumL genConsDecl env1 cs
genTypeDecl env (TypeDecl _ n vs ty)
  = ( resetScope env2
    , CTypeSyn (genQName True env2 $ qualifyWith (moduleId env) n)
               (genVisibility env2 n)
               (zip idxs $ map idName vs)
               ty'
    )
  where (env1, idxs) = mapAccumL genTVarIndex env vs
        (env2, ty' ) = genTypeExpr env1 ty
genTypeDecl env (NewtypeDecl _ n vs (NewConstrDecl p nvs nc ty))
  = (resetScope env2
    , CType (genQName True env2 $ qualifyWith (moduleId env) n)
            (genVisibility env2 n)
            (zip idxs $ map idName vs)
            [nc']
    ) where (env1, idxs) = mapAccumL genTVarIndex env vs
            (env2, nc' ) = genConsDecl env1 (ConstrDecl p nvs nc [ty])
genTypeDecl _ _
  = internalError "GenAbstractCurry.genTypeDecl: unexpected declaration"

--
genConsDecl :: AbstractEnv -> ConstrDecl -> (AbstractEnv, CConsDecl)
genConsDecl env (ConstrDecl _ _ n vs)
  = ( env', CCons (genQName False env' $ qualifyWith (moduleId env) n)
                  (length vs)
                  (genVisibility env' n)
                  vs'
    ) where (env', vs') = mapAccumL genTypeExpr env vs
genConsDecl env (ConOpDecl p vs ty1 op ty2)
  = genConsDecl env (ConstrDecl p vs op [ty1, ty2])

--
genTypeExpr :: AbstractEnv -> TypeExpr -> (AbstractEnv, CTypeExpr)
genTypeExpr env (ConstructorType q vs)
  = (env', CTCons (genQName True env' q) vs')
  where (env', vs') = mapAccumL genTypeExpr env vs
genTypeExpr env (VariableType ident) = case getTVarIndex env ident of
  Just ix -> (env , CTVar (ix , idName ident))
  Nothing -> (env', CTVar (idx, idName ident))
  where (env', idx) = genTVarIndex env ident
genTypeExpr env (TupleType     tys) = genTypeExpr env $ case tys of
   []   -> ConstructorType qUnitId []
   [ty] -> ty
   _    -> ConstructorType (qTupleId $ length tys) tys
genTypeExpr env (ListType       ty)
  = genTypeExpr env $ ConstructorType qListId [ty]
genTypeExpr env (ArrowType ty1 ty2) = (env2, CFuncType ty1' ty2')
  where (env1, ty1') = genTypeExpr env  ty1
        (env2, ty2') = genTypeExpr env1 ty2
genTypeExpr env (RecordType fss mr) = case mr of
  Nothing -> (env1, CRecordType (zip ls' ts') Nothing)
  Just tvar@(VariableType _) ->
    let (env2, CTVar iname) = genTypeExpr env1 tvar
    in  (env2, CRecordType (zip ls' ts') (Just iname))
  Just r@(RecordType _ _) ->
    let (env2, CRecordType fields rbase) = genTypeExpr env1 r
        fields' = foldr (uncurry insertEntry) fields (zip ls' ts')
    in  (env2, CRecordType fields' rbase)
  _ -> internalError "GenAbstractCurry.gegnTypeExpr: illegal record base"
  where
  (ls  , ts ) = unzip $ concatMap (\ (ls1,ty) -> map (\l -> (l,ty)) ls1) fss
  (env1, ts') = mapAccumL genTypeExpr env ts
  ls'        = map idName ls

genOpDecl :: AbstractEnv -> Decl -> [COpDecl]
genOpDecl env (InfixDecl _ fix prec ops) = map genCOp (reverse ops)
  where
  genCOp op = COp (genQName False env $ qualifyWith (moduleId env) op)
                  (genFixity fix)
                  (fromInteger prec)

  genFixity InfixL = CInfixlOp
  genFixity InfixR = CInfixrOp
  genFixity Infix  = CInfixOp
genOpDecl _ _ = internalError "GenAbstractCurry.genOpDecl: no infix declaration"

-- Generate an AbstractCurry function declaration from a list of CurrySyntax
-- function declarations.
-- NOTES:
--   - every declaration in 'decls' must declare exactly one function.
--   - since inferred types are internally represented in flat style,
--     all type variables are renamed with generated symbols when
--     generating typed AbstractCurry.
genFuncDecl :: Bool -> AbstractEnv -> (Ident, [Decl]) -> (AbstractEnv, CFuncDecl)
genFuncDecl isLocal env (ident, decls)
  | null decls = internalError $ "GenAbstractCurry.genFuncDecl: "
              ++ "missing declaration for function \"" ++ show ident ++ "\""
  | otherwise  = (env3, CFunc qname arity visibility typeexpr rule)
  where
  qname       = genQName False env $ qualify ident
  visibility  = genVisibility env ident
  evalannot   = CFlex
--   evalannot   = case find isEvalAnnot decls of
--                   Nothing -> CFlex
--                   Just (EvalAnnot _ _ ea) -> genEvalAnnot ea
--                   _ -> internalError "Gen.GenAbstractCurry.genFuncDecl: no Eval Annotation"
  (env1, mtype) = case genFuncType env decls of
                  Nothing        -> (env, Nothing)
                  Just (env', t) -> (env', Just t)
  (env2, rules) = case find isFunctionDecl decls of
                  Nothing -> (env1, [])
                  Just (FunctionDecl _ _ eqs) -> mapAccumL genRule env1 eqs
                  _ -> internalError "Gen.GenAbstractCurry.genFuncDecl: no FunctionDecl"
  mexternal   = genExternal `fmap` find isExternal decls
  arity       = compArity mtype rules
  typeexpr    = fromMaybe (CTCons ("Prelude", "untyped") []) mtype
  rule        = compRule evalannot rules mexternal
  env3        = if isLocal then env1 else resetScope env2

  genFuncType env' decls'
    | acytype == UntypedAcy = genTypeSig  env' `fmap` find isTypeSig decls'
    | acytype == TypedAcy   = genTypeExpr env' `fmap` mftype
    | otherwise             = Nothing
    where
    acytype = acyType env
    mftype | isLocal   = lookupType ident (typeEnv env)
           | otherwise = qualLookupType (qualifyWith (moduleId env) ident)
                          (typeEnv env)

  genTypeSig env' (TypeSig          _ _ ts) = genTypeExpr env' ts
  genTypeSig env' (ExternalDecl _ _ _ _ ts) = genTypeExpr env' ts
  genTypeSig _    _ =
    internalError "GenAbstractCurry.genFuncDecl.genTypeSig: no pattern match"

  genExternal (ExternalDecl _ _ mname ident' _)
    = CExternal (fromMaybe (idName ident') mname)
  genExternal (FlatExternalDecl _ [ident'])
    = CExternal (idName ident')
  genExternal _
    = internalError $ "GenAbstractCurry.genExternal: "
      ++ "illegal external declaration occured"

  compArity Nothing   [] = internalError $ "GenAbstractCurry.compArity: "
                           ++ "unable to compute arity for function \""
                           ++ show ident ++ "\""
  compArity (Just ty) [] = compArityFromType ty
  compArity _         (CRule patts _ _ : _) = length patts

  compArityFromType (CTVar         _) = 0
  compArityFromType (CFuncType  _ t2) = 1 + compArityFromType t2
  compArityFromType (CTCons      _ _) = 0
  compArityFromType (CRecordType _ _) =
    internalError "GenAbstractCurry.genFuncDecl.compArityFromType: record type"

  compRule _  [] Nothing  = internalError $ "GenAbstractCurry.compRule: "
                            ++ "missing rule for function \""
                            ++ show ident ++ "\""
  compRule _  [] (Just e) = e
  compRule ea rs _        = CRules ea rs

--
genRule :: AbstractEnv -> Equation -> (AbstractEnv, CRule)
genRule env (Equation pos lhs rhs)
  = let (env1, patts ) = mapAccumL (genPattern pos)
                                   (beginScope env)
                                   (simplifyLhs lhs)
        (env2, locals) = genLocalDecls env1 (simplifyRhsLocals rhs)
        (env3, crhss ) = mapAccumL (genRhs pos) env2 (simplifyRhsExpr rhs)
    in  (endScope env3, CRule patts crhss locals)

--
genRhs :: Position -> AbstractEnv -> (Expression, Expression)
       -> (AbstractEnv, (CExpr, CExpr))
genRhs p env (cond, expr)
  = let (env1, cond') = genExpr p env cond
        (env2, expr') = genExpr p env1 expr
    in  (env2, (cond', expr'))

-- NOTE: guarded expressions and 'where' declarations in local pattern
-- declarations are not supported in PAKCS
genLocalDecls :: AbstractEnv -> [Decl] -> (AbstractEnv, [CLocalDecl])
genLocalDecls env decls
  = genLocals (foldl genLocalIndex env decls)
              (funcDecls (foldl partitionDecl emptyPartition decls))
              decls
 where
  genLocalIndex env' (PatternDecl _ constr _)
    = genLocalPatternIndex env' constr
  genLocalIndex env' (ExtraVariables _ idents)
    = let (env'', _) = mapAccumL genVarIndex env' idents
      in  env''
  genLocalIndex env' _ = env'

  genLocalPatternIndex env' (VariablePattern ident)
    = fst $ genVarIndex env' ident
  genLocalPatternIndex env' (ConstructorPattern _ args)
    = foldl genLocalPatternIndex env' args
  genLocalPatternIndex env' (InfixPattern c1 _ c2)
    = foldl genLocalPatternIndex env' [c1, c2]
  genLocalPatternIndex env' (ParenPattern c)
    = genLocalPatternIndex env' c
  genLocalPatternIndex env' (TuplePattern _ args)
    = foldl genLocalPatternIndex env' args
  genLocalPatternIndex env' (ListPattern _ args)
    = foldl genLocalPatternIndex env' args
  genLocalPatternIndex env' (AsPattern ident c)
    = genLocalPatternIndex (fst $ genVarIndex env' ident) c
  genLocalPatternIndex env' (LazyPattern _ c)
    = genLocalPatternIndex env' c
  genLocalPatternIndex env' (RecordPattern fields mc)
    = let env'' = foldl genLocalPatternIndex env' (map fieldTerm fields)
      in  maybe env'' (genLocalPatternIndex env'') mc
  genLocalPatternIndex env' _ = env'

  -- The association list 'fdecls' is necessary because function
  -- rules may not be together in the declaration list
  genLocals :: AbstractEnv -> [(Ident, [Decl])] -> [Decl]
            -> (AbstractEnv, [CLocalDecl])
  genLocals env' _ [] = (env', [])
  genLocals env' fdecls ((FunctionDecl _ ident _):decls1)
    = let (env1, funcdecl) = genLocalFuncDecl (beginScope env') fdecls ident
          (env2, locals  ) = genLocals (endScope env1) fdecls decls1
      in  (env2, funcdecl:locals)
  genLocals env' fdecls ((ExternalDecl _ _ _ ident _):decls1)
    = let (env1, funcdecl) = genLocalFuncDecl (beginScope env') fdecls ident
          (env2, locals  ) = genLocals (endScope env1) fdecls decls1
      in  (env2, funcdecl:locals)
  genLocals env' fdecls ((FlatExternalDecl pos idents):decls1)
    | null idents = genLocals env' fdecls decls1
    | otherwise
    = let (env1, funcdecl) = genLocalFuncDecl (beginScope env') fdecls (head idents)
          (env2, locals  ) = genLocals (endScope env1) fdecls (FlatExternalDecl pos (tail idents):decls1)
      in  (env2, funcdecl:locals)
  genLocals env' fdecls (PatternDecl pos constr rhs : decls1)
    = let (env1, patt   ) = genLocalPattern pos env' constr
          (env2, plocals) = genLocalDecls (beginScope env1)
                              (simplifyRhsLocals rhs)
          (env3, expr   ) = genLocalPattRhs pos env2 (simplifyRhsExpr rhs)
          (env4, locals ) = genLocals (endScope env3) fdecls decls1
      in  (env4, CLocalPat patt expr plocals:locals)
  genLocals env' fdecls ((ExtraVariables pos idents):decls1)
    | null idents  = genLocals env' fdecls decls1
    | otherwise
      = let ident  = head idents
            idx    = fromMaybe
                  (internalError ("GenAbstractCurry.genLocals: cannot find index"
                ++ " for free variable \""
                ++ show ident ++ "\""))
                  (getVarIndex env' ident)
            decls' = ExtraVariables pos (tail idents) : decls1
            (env'', locals) = genLocals env' fdecls decls'
        in (env'', CLocalVar (idx, idName ident) : locals)
  genLocals env' fdecls ((TypeSig _ _ _):decls1)
    = genLocals env' fdecls decls1
  genLocals _ _ decl = internalError ("GenAbstractCurry.genLocals: unexpected local declaration: \n" ++ show (head decl))

  genLocalFuncDecl :: AbstractEnv -> [(Ident, [Decl])] -> Ident
                   -> (AbstractEnv, CLocalDecl)
  genLocalFuncDecl env' fdecls ident
    = let fdecl = fromMaybe
              (internalError ("GenAbstractCurry.genLocalFuncDecl: missing declaration"
                  ++ " for local function \""
                  ++ show ident ++ "\""))
              (lookup ident fdecls)
          (_, funcdecl) = genFuncDecl True env' (ident, fdecl)
      in  (env', CLocalFunc funcdecl)

  genLocalPattern pos env' (LiteralPattern l) = case l of
    String _ cs
      -> genLocalPattern pos env' $ ListPattern [] $ map (LiteralPattern . Char noRef) cs
    _ -> (env', CPLit $ genLiteral l)
  genLocalPattern _ env' (VariablePattern v) = case getVarIndex env' v of
    Nothing  -> internalError $ "GenAbstractCurry.genLocalPattern: "
      ++ "cannot find index" ++ " for pattern variable \"" ++ show v ++ "\""
    Just idx -> (env', CPVar (idx, idName v))
  genLocalPattern pos env' (ConstructorPattern qident args)
    = let (env'', args') = mapAccumL (genLocalPattern pos) env' args
      in (env'', CPComb (genQName False env' qident) args')
  genLocalPattern pos env' (InfixPattern larg qident rarg)
    = genLocalPattern pos env' (ConstructorPattern qident [larg, rarg])
  genLocalPattern pos env' (ParenPattern patt)
    = genLocalPattern pos env' patt
  genLocalPattern pos env' (TuplePattern _ args)
    | len == 0  = genLocalPattern pos env' (ConstructorPattern qUnitId [])
    | len == 1  = genLocalPattern pos env' (head args)
    | otherwise = genLocalPattern pos env' (ConstructorPattern (qTupleId len) args) -- len > 1
    where len = length args
  genLocalPattern pos env' (ListPattern _ args)
    = genLocalPattern pos env'
      (foldr (\p1 p2 -> ConstructorPattern qConsId [p1,p2])
        (ConstructorPattern qNilId [])
        args)
  genLocalPattern _ _ (NegativePattern _ _)
    = internalError "negative patterns are not supported in AbstractCurry"
  genLocalPattern pos env' (AsPattern ident cterm)
    = let (env1, patt) = genLocalPattern pos env' cterm
          idx          = fromMaybe
                (internalError ("GenAbstractCurry.genLocalPattern: cannot find index"
                    ++ " for alias variable \""
                    ++ show ident ++ "\""))
                (getVarIndex env1 ident)
      in  (env1, CPAs (idx, idName ident) patt)
  genLocalPattern pos env' (LazyPattern _ cterm)
    = let (env'', patt) = genLocalPattern pos env' cterm
      in  (env'', CPLazy patt)
  genLocalPattern pos env' (RecordPattern fields mr)
    = let (env1, fields') = mapAccumL (genField genLocalPattern) env' fields
          (env2, mr'    ) = case mr of
                              Nothing -> (env1, Nothing)
                              Just r  -> let (envX, patt) = genLocalPattern pos env1 r in (envX, Just patt)
      in  (env2, CPRecord fields' mr')
  genLocalPattern _ _ _ = internalError "GenAbstractCurry.genLocalDecls.genLocalPattern: no pattern match"

  genLocalPattRhs pos env' [(Variable _, expr)]
    = genExpr pos env' expr
  genLocalPattRhs _ _ _
    = internalError ("guarded expressions in pattern declarations"
      ++ " are not supported in AbstractCurry")

--
genExpr :: Position -> AbstractEnv -> Expression -> (AbstractEnv, CExpr)
genExpr pos env (Literal l) = case l of
  String _ cs -> genExpr pos env $ List [] $ map (Literal . Char noRef) cs
  _           -> (env, CLit $ genLiteral l)
genExpr _ env   (Variable v)
  | isJust midx     = (env, CVar (fromJust midx, idName ident))
  | v == qSuccessId = (env, CSymbol $ genQName False env qSuccessFunId)
  | otherwise       = (env, CSymbol $ genQName False env v)
  where
  ident = unqualify v
  midx  = getVarIndex env ident
genExpr _   env (Constructor c) = (env, CSymbol $ genQName False env c)
genExpr pos env (Paren    expr) = genExpr pos env expr
genExpr pos env (Typed  expr _) = genExpr pos env expr
genExpr pos env (Tuple  _ args) = genExpr pos env $ case args of
  []  -> Variable qUnitId
  [x] -> x
  _   -> foldl Apply (Variable $ qTupleId $ length args) args
genExpr pos env (List _ args)
  = let cons = Constructor qConsId
        nil  = Constructor qNilId
    in  genExpr pos env (foldr (Apply . Apply cons) nil args)
genExpr pos env (ListCompr _ expr stmts)
  = let (env1, stmts') = mapAccumL (genStatement pos) (beginScope env) stmts
        (env2, expr' )  = genExpr pos env1 expr
    in  (endScope env2, CListComp expr' stmts')
genExpr pos env (EnumFrom expr)
  = genExpr pos env (Apply (Variable qEnumFromId) expr)
genExpr pos env (EnumFromThen expr1 expr2)
  = genExpr pos env (Apply (Apply (Variable qEnumFromThenId) expr1) expr2)
genExpr pos env (EnumFromTo expr1 expr2)
  = genExpr pos env (Apply (Apply (Variable qEnumFromToId) expr1) expr2)
genExpr pos env (EnumFromThenTo expr1 expr2 expr3)
  = genExpr pos env (Apply (Apply (Apply (Variable qEnumFromThenToId)
          expr1) expr2) expr3)
genExpr pos env (UnaryMinus _ expr)
  = genExpr pos env (Apply (Variable qNegateId) expr)
genExpr pos env (Apply expr1 expr2)
  = let (env1, expr1') = genExpr pos env expr1
        (env2, expr2') = genExpr pos env1 expr2
    in  (env2, CApply expr1' expr2')
genExpr pos env (InfixApply expr1 op expr2)
  = genExpr pos env (Apply (Apply (opToExpr op) expr1) expr2)
genExpr pos env (LeftSection expr op)
  = let ident  = freshVar env "x"
        patt   = VariablePattern ident
        var    = Variable (qualify ident)
        applic = Apply (Apply (opToExpr op) expr) var
    in  genExpr pos env (Lambda noRef [patt] applic)
genExpr pos env (RightSection op expr)
  = let ident  = freshVar env "x"
        patt   = VariablePattern ident
        var    = Variable (qualify ident)
        applic = Apply (Apply (opToExpr op) var) expr
    in  genExpr pos env (Lambda noRef [patt] applic)
genExpr pos env (Lambda _ params expr)
  = let (env1, params') = mapAccumL (genPattern pos) (beginScope env) params
        (env2, expr'  )   = genExpr pos env1 expr
    in  (endScope env2, CLambda params' expr')
genExpr pos env (Let decls expr)
  = let (env1, decls') = genLocalDecls (beginScope env) decls
        (env2, expr' ) = genExpr pos env1 expr
    in  (endScope env2, CLetDecl decls' expr')
genExpr pos env (Do stmts expr)
  = let (env1, stmts') = mapAccumL (genStatement pos) (beginScope env) stmts
        (env2, expr' )  = genExpr pos env1 expr
    in  (endScope env2, CDoExpr (stmts' ++ [CSExpr expr']))
genExpr pos env (IfThenElse _ expr1 expr2 expr3)
  = genExpr pos env (Apply (Apply (Apply (Variable qIfThenElseId)
                    expr1) expr2) expr3)
genExpr pos env (Case _ _ expr alts)
  = let (env1, expr') = genExpr pos env expr
        (env2, alts') = mapAccumL genBranchExpr env1 alts
    in  (env2, CCase expr' alts')
genExpr _ env (RecordConstr fields)
  = let (env1, fields') = mapAccumL (genField genExpr) env fields
    in  (env1, CRecConstr fields')
genExpr pos env (RecordSelection expr label)
  = let (env1, expr') = genExpr pos env expr
    in  (env1, CRecSelect expr' $ idName label)
genExpr pos env (RecordUpdate fields expr)
  = let (env1, fields') = mapAccumL (genField genExpr) env fields
        (env2, expr'  ) = genExpr pos env1 expr
    in  (env2, CRecUpdate fields' expr')

--
genStatement :: Position -> AbstractEnv -> Statement -> (AbstractEnv, CStatement)
genStatement pos env (StmtExpr _ expr)
  = let (env', expr') = genExpr pos env expr
    in  (env', CSExpr expr')
genStatement _ env (StmtDecl decls)
  = let (env', decls') = genLocalDecls env decls
    in  (env', CSLet decls')
genStatement pos env (StmtBind _ patt expr)
  = let (env1, expr') = genExpr pos env expr
        (env2, patt') = genPattern pos env1 patt
    in  (env2, CSPat patt' expr')

-- NOTE: guarded expressions and local declarations in case branches
-- are not supported in PAKCS
genBranchExpr :: AbstractEnv -> Alt -> (AbstractEnv, CBranchExpr)
genBranchExpr env (Alt p pat rhs)
  = let (env1, pat') = genPattern p (beginScope env) pat
        (env2, be  ) = genBranch env1 pat' $ simplifyRhsExpr rhs
    in  (endScope env2, be)
  where
  genBranch env' pat' [(Variable _, expr)] -- no guards!
    = let (env2, expr') = genExpr p env' expr
      in  (env2, CBranch pat' expr')
  genBranch env' pat' bs
    = let (env2, bs') = mapAccumL (genRhs p) env' bs
      in  (env2, CGuardedBranch pat' bs')

--
genPattern :: Position -> AbstractEnv -> ConstrTerm -> (AbstractEnv, CPattern)
genPattern pos env (LiteralPattern l) = case l of
  String _ cs -> genPattern pos env $ ListPattern [] $ map (LiteralPattern . Char noRef) cs
  _           -> (env, CPLit $ genLiteral l)
genPattern _ env (VariablePattern v)
  = let (env', idx) = genVarIndex env v
    in  (env', CPVar (idx, idName v))
genPattern pos env (ConstructorPattern qident args)
  = let (env', args') = mapAccumL (genPattern pos) env args
    in  (env', CPComb (genQName False env qident) args')
genPattern pos env (InfixPattern larg qident rarg)
  = genPattern pos env $ ConstructorPattern qident [larg, rarg]
genPattern pos env (ParenPattern patt)
  = genPattern pos env patt
genPattern pos env (TuplePattern _ args) = genPattern pos env $ case args of
  []   -> ConstructorPattern qUnitId []
  [ty] -> ty
  _    -> ConstructorPattern (qTupleId $ length args) args
genPattern pos env (ListPattern _ args) = genPattern pos env $
  foldr (\x1 x2 -> ConstructorPattern qConsId [x1, x2])
        (ConstructorPattern qNilId [])
        args
genPattern _ _ (NegativePattern _ _)
  = internalError "negative patterns are not supported in AbstractCurry"
genPattern pos env (AsPattern ident cterm)
  = let (env1, patt) = genPattern pos env cterm
        (env2, idx ) = genVarIndex env1 ident
    in  (env2, CPAs (idx, idName ident) patt)
genPattern pos env (LazyPattern _ cterm)
  = let (env', patt) = genPattern pos env cterm
    in  (env', CPLazy patt)
genPattern pos env (FunctionPattern qident cterms)
  = let (env', patts) = mapAccumL (genPattern pos) env cterms
    in  (env', CPFuncComb (genQName False env qident) patts)
genPattern pos env (InfixFuncPattern cterm1 qident cterm2)
  = genPattern pos env (FunctionPattern qident [cterm1, cterm2])
genPattern pos env (RecordPattern fields mr)
  = let (env1, fields') = mapAccumL (genField genPattern) env fields
        (env2, mr')     = case mr of
          Nothing -> (env1, Nothing)
          Just r  -> let (env', patt) = genPattern pos env1 r in (env', Just patt)
    in  (env2, CPRecord fields' mr')

--
genField :: (Position -> AbstractEnv -> a -> (AbstractEnv, b))
         -> AbstractEnv -> Field a -> (AbstractEnv, CField b)
genField genTerm env (Field p l t) = (env1, (idName l, t'))
  where (env1, t') = genTerm p env t

--
genLiteral :: Literal -> CLiteral
genLiteral (Char  _ c) = CCharc  c
genLiteral (Int   _ i) = CIntc   i
genLiteral (Float _ f) = CFloatc f
genLiteral _           = internalError "GenAbstractCurry.genLiteral: unsupported literal"

-- |Create a qualified AbstractCurry identifier from a Curry 'QualIdent'.
--
-- * Some prelude identifiers are not qualified. The first check ensures
--   that they get a correct qualifier.
-- * The test for unqualified identifiers is necessary to qualify
--   them correctly in the untyped AbstractCurry representation.
genQName :: Bool -> AbstractEnv -> QualIdent -> QName
genQName isTypeCons env qident
  | isPreludeSymbol qident = genQualName $ qualQualify preludeMIdent qident
  | isQualified     qident = genQualName qident
  | otherwise              = genQualName $ getQualIdent $ unqualify qident
  where
  genQualName qid = ( moduleName $ fromMaybe (moduleId env) $ qidModule qid
                    , idName $ qidIdent qid
                    )
-- TODO@bjp (2012-01-04): Disabled
--   genQualName qid = (moduleName mid, name ident)
--     where (mmid, ident) = (qidModule qid, qidIdent qid)
--           mid           = maybe (moduleId env)
--                           (`sureLookupAlias` aliases env)
--                           mmid

  getQualIdent ident
    | isTypeCons = case lookupTC ident $ tconsEnv env of
        [info] -> origName info
        _      -> qualifyWith (moduleId env) ident
    | otherwise  = case lookupValue ident $ typeEnv env of
        [info] -> origName info
        _      -> qualifyWith (moduleId env) ident

--
genVisibility :: AbstractEnv -> Ident -> CVisibility
genVisibility env ident
  | isExported env ident = Public
  | otherwise            = Private

-------------------------------------------------------------------------------
-- This part defines an environment containing all necessary information
-- for generating the AbstractCurry representation of a CurrySyntax term.

-- |Data type for representing an AbstractCurry generator environment
data AbstractEnv = AbstractEnv
  { moduleId   :: ModuleIdent         -- ^name of the module
  , typeEnv    :: ValueEnv            -- ^known values
  , tconsEnv   :: TCEnv               -- ^known type constructors
  , exports    :: Set.Set Ident       -- ^exported symbols
--   , aliases    :: AliasEnv            -- ^module aliases
  , varIndex   :: Int                 -- ^counter for variable indices
  , tvarIndex  :: Int                 -- ^counter for type variable indices
  , varScope   :: [Map.Map Ident Int] -- ^stack of variable tables
  , tvarScope  :: [Map.Map Ident Int] -- ^stack of type variable tables
  , acyType    :: AbstractType        -- ^type of code to be generated
  } deriving Show

-- |Data type representing the type of AbstractCurry code to be generated
-- (typed infered or untyped (i.e. type signated))
data AbstractType
  = TypedAcy
  | UntypedAcy
    deriving (Eq, Show)

-- |Initialize the AbstractCurry generator environment
abstractEnv :: AbstractType -> CompilerEnv -> Module -> AbstractEnv
abstractEnv absType env (Module mid exps _ decls) = AbstractEnv
  { moduleId  = mid
  , typeEnv   = valueEnv env
  , tconsEnv  = tyConsEnv env
  , exports   = foldl (buildExportTable mid decls) Set.empty exps'
--   , aliases   = aliasEnv env
  , varIndex  = 0
  , tvarIndex = 0
  , varScope  = [Map.empty]
  , tvarScope = [Map.empty]
  , acyType   = absType
  }
 where exps' = maybe (buildExports mid decls) (\ (Exporting _ es) -> es) exps

-- Generates a list of exports for all specified top level declarations
buildExports :: ModuleIdent -> [Decl] -> [Export]
buildExports _ [] = []
buildExports mid (DataDecl _ ident _ _:ds)
  = ExportTypeAll (qualifyWith mid ident) : buildExports mid ds
buildExports mid ((NewtypeDecl _ ident _ _):ds)
  = ExportTypeAll (qualifyWith mid ident) : buildExports mid ds
buildExports mid ((TypeDecl _ ident _ _):ds)
  = Export (qualifyWith mid ident) : buildExports mid ds
buildExports mid ((FunctionDecl _ ident _):ds)
  = Export (qualifyWith mid ident) : buildExports mid ds
buildExports mid (ExternalDecl _ _ _ ident _ : ds)
  = Export (qualifyWith mid ident) : buildExports mid ds
buildExports mid (FlatExternalDecl _ idents : ds)
  = map (Export . qualifyWith mid) idents ++ buildExports mid ds
buildExports mid (_:ds) = buildExports mid ds

-- Builds a table containing all exported (i.e. public) identifiers
-- from a module.
buildExportTable :: ModuleIdent -> [Decl] -> Set.Set Ident -> Export
                 -> Set.Set Ident
buildExportTable mid _ exptab (Export qident)
  | isJust (localIdent mid qident)
  = insertExportedIdent exptab (unqualify qident)
  | otherwise = exptab
buildExportTable mid _ exptab (ExportTypeWith qident ids)
  | isJust (localIdent mid qident)
  = foldl insertExportedIdent
          (insertExportedIdent exptab (unqualify qident))
          ids
  | otherwise  = exptab
buildExportTable mid decls exptab (ExportTypeAll qident)
  | isJust ident'
  = foldl insertExportedIdent
          (insertExportedIdent exptab ident)
          (maybe [] getConstrIdents (find (isDataDeclOf ident) decls))
  | otherwise = exptab
  where
  ident' = localIdent mid qident
  ident  = fromJust ident'
buildExportTable _ _ exptab (ExportModule _) = exptab

--
insertExportedIdent :: Set.Set Ident -> Ident -> Set.Set Ident
insertExportedIdent env ident = Set.insert ident env

--
getConstrIdents :: Decl -> [Ident]
getConstrIdents (DataDecl _ _ _ cs) = map getConstr cs
  where getConstr (ConstrDecl  _ _  c _) = c
        getConstr (ConOpDecl _ _ _ op _) = op
getConstrIdents _ = internalError "GenAbstractCurry.getConstrIdents: no data declaration"

-- Checks whether an identifier is exported or not.
isExported :: AbstractEnv -> Ident -> Bool
isExported env ident = Set.member ident $ exports env

-- Generates an unique index for the  variable 'ident' and inserts it
-- into the  variable table of the current scope.
genVarIndex :: AbstractEnv -> Ident -> (AbstractEnv, Int)
genVarIndex env ident
  = let idx            = varIndex env
        (vtab : vtabs) = varScope env
    in  ( env { varIndex = idx + 1
              , varScope = Map.insert ident idx vtab : vtabs
              }
        , idx
        )

-- Generates an unique index for the type variable 'ident' and inserts it
-- into the type variable table of the current scope.
genTVarIndex :: AbstractEnv -> Ident -> (AbstractEnv, Int)
genTVarIndex env ident
  = let idx            = tvarIndex env
        (vtab : vtabs) = tvarScope env
    in  ( env { tvarIndex = idx + 1
              , tvarScope = Map.insert ident idx vtab : vtabs
              }
        , idx
        )

-- Looks up the unique index for the variable 'ident' in the
-- variable table of the current scope.
getVarIndex :: AbstractEnv -> Ident -> Maybe Int
getVarIndex env ident = Map.lookup ident $ head $ varScope env

-- Looks up the unique index for the type variable 'ident' in the type
-- variable table of the current scope.
getTVarIndex :: AbstractEnv -> Ident -> Maybe Int
getTVarIndex env ident = Map.lookup ident $ head $ tvarScope env

-- Generates an indentifier which doesn't occur in the variable table
-- of the current scope.
freshVar :: AbstractEnv -> String -> Ident
freshVar env vname = genFreshVar env vname (0 :: Integer)
  where
  genFreshVar env1 name1 idx
    | isJust (getVarIndex env1 ident)
    = genFreshVar env1 name1 (idx + 1)
    | otherwise
    = ident
    where ident = mkIdent $ name1 ++ show idx

-- Sets the index counter back to zero and deletes all stack entries.
resetScope :: AbstractEnv -> AbstractEnv
resetScope env = env
  { varIndex  = 0
  , tvarIndex = 0
  , varScope  = [Map.empty]
  , tvarScope = [Map.empty]
  }

-- Starts a new scope, i.e. copies and pushes the variable table of the current
-- scope onto the top of the stack
beginScope :: AbstractEnv -> AbstractEnv
beginScope env = env { varScope  = head vs : vs, tvarScope = head tvs : tvs }
  where
  vs  = varScope env
  tvs = tvarScope env

-- End the current scope, i.e. pops and deletes the variable table of the
-- current scope from the top of the stack.
endScope :: AbstractEnv -> AbstractEnv
endScope env = env { varScope  = newVarScope, tvarScope = newTVarScope }
  where
  newVarScope  = if isSingleton  vs then  vs else tail  vs
  newTVarScope = if isSingleton tvs then tvs else tail tvs
  vs           = varScope env
  tvs          = tvarScope env

-------------------------------------------------------------------------------
-- Miscellaneous...

-- Some identifiers...
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

-- The following functions check whether a declaration is of a certain kind
isFunctionDecl :: Decl -> Bool
isFunctionDecl (FunctionDecl _ _ _) = True
isFunctionDecl _                    = False

isExternal :: Decl -> Bool
isExternal (ExternalDecl _ _ _ _ _) = True
isExternal (FlatExternalDecl   _ _) = True
isExternal _                        = False

-- Checks, whether a declaration is the data declaration of 'ident'.
isDataDeclOf :: Ident -> Decl -> Bool
isDataDeclOf i (DataDecl _ j _ _) = i == j
isDataDeclOf _ _                  = False

-- Checks, whether a symbol is defined in the Prelude.
isPreludeSymbol :: QualIdent -> Bool
isPreludeSymbol qident
   = let (mmid, ident) = (qidModule qident, qidIdent qident)
     in (isJust mmid && preludeMIdent == fromJust mmid)
        || elem ident [unitId, listId, nilId, consId]
        || isTupleId ident

-- Converts an infix operator to an expression
opToExpr :: InfixOp -> Expression
opToExpr (InfixOp    op) = Variable op
opToExpr (InfixConstr c) = Constructor c

-- Looks up the type of a qualified symbol in the type environment and
-- converts it to a CurrySyntax type term.
qualLookupType :: QualIdent -> ValueEnv -> Maybe TypeExpr
qualLookupType qident tyEnv = case qualLookupValue qident tyEnv of
  [Value _ _ (ForAll _ ty)] -> Just $ fromType ty
  _                         -> Nothing

-- Looks up the type of a symbol in the type environment and
-- converts it to a CurrySyntax type term.
lookupType :: Ident -> ValueEnv -> Maybe TypeExpr
lookupType ident tyEnv = case lookupValue ident tyEnv of
  [Value _ _ (ForAll _ ty)] -> Just $ fromType ty
  _                         -> Nothing

-- The following functions transform left-hand-side and right-hand-side terms
-- for a better handling
simplifyLhs :: Lhs -> [ConstrTerm]
simplifyLhs = snd . flatLhs

simplifyRhsExpr :: Rhs -> [(Expression, Expression)]
simplifyRhsExpr (SimpleRhs _ e _) = [(Variable qSuccessId, e)]
simplifyRhsExpr (GuardedRhs gs _) = map (\ (CondExpr _ g e) -> (g, e)) gs

simplifyRhsLocals :: Rhs -> [Decl]
simplifyRhsLocals (SimpleRhs _ _ locals) = locals
simplifyRhsLocals (GuardedRhs  _ locals) = locals

-- Insert a value under a key into an association list. If the list
-- already contains a value for that key, the old value is replaced.
insertEntry :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertEntry k v []             = [(k, v)]
insertEntry k v ((l, w) : kvs)
  | k == l    = (k, v) : kvs
  | otherwise = (l, w) : insertEntry k v kvs

-- Return 'True' iff a list is a singleton list (contains exactly one element)
isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _   = False
