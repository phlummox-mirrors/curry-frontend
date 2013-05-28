{- |
    Module      :  $Header$
    Description :  
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The main function of this module transforms the abstract syntax tree by
    adding dictionary parameters where necessary. 
-}

module Transformations.Dictionaries (insertDicts) where

import Curry.Base.Ident
import CompilerEnv
import Curry.Syntax
import Env.ClassEnv
import Checks.TypeClassesCheck (sep)
import Base.Messages

import Base.Types as BT

import Control.Monad.State as S

-- ----------------------------------------------------------------------------
-- the state monad used
-- ----------------------------------------------------------------------------

type DI = S.State DIState

data DIState = DIState 
  { theClassEnv :: ClassEnv
  }

initState :: ClassEnv -> DIState
initState cEnv = DIState cEnv

runDI :: DI a -> DIState -> a
runDI comp init0 = let (a, _s) = S.runState comp init0 in a

getClassEnv :: DI ClassEnv
getClassEnv = S.gets theClassEnv

-- ----------------------------------------------------------------------------
-- the transformation functions
-- ----------------------------------------------------------------------------

-- |The main function of this module. It descends into the syntax tree and
-- inserts dictionary parameters (in function declarations and in expressions)
insertDicts :: Module -> CompilerEnv -> Module
insertDicts mdl cEnv = 
  runDI (diModule mdl) (initState $ classEnv cEnv)   

-- |convert a whole module
diModule :: Module -> DI Module
diModule (Module m e i ds) = Module m e i `liftM` (mapM diDecl ds)
  
-- |convert function declarations
diDecl :: Decl -> DI Decl
diDecl (FunctionDecl p (Just cty) id0 eqs) = do
  cEnv <- getClassEnv
  let cty'  = mirrorCT cty
      -- we have to reduce the context before adding dictionary parameters, 
      -- because the recorded context is the "raw" context 
      cty'' = (reduceContext cEnv $ fst $ cty', snd cty')
  FunctionDecl p (Just cty) id0 `liftM` (mapM (diEqu cty'' $ show id0) eqs)
diDecl (FunctionDecl _ Nothing _ _) = internalError "no type info in diDecl"
-- TODO: convert pattern declarations!
diDecl f@(PatternDecl _p (Just _cty) _ps _rhs) = return f 
diDecl (PatternDecl _ Nothing _ _) = internalError "no type info in diDecl"
diDecl f = return f

-- |transform an equation
-- Takes the type of the corresponding function declaration, and the name
-- of the function 
diEqu :: ConstrType -> String -> Equation -> DI Equation
diEqu cty fun (Equation p lhs rhs)= 
  liftM2 (Equation p) (diLhs cty fun lhs) (diRhs cty fun rhs)

-- |transform right hand sides
diRhs :: ConstrType -> String -> Rhs -> DI Rhs
diRhs cty fun (SimpleRhs p e ds) = 
  liftM2 (SimpleRhs p) (diExpr cty fun e) (mapM diDecl ds)
diRhs cty fun (GuardedRhs ces ds) = 
  liftM2 GuardedRhs (mapM (diCondExpr cty fun) ces) (mapM diDecl ds)

  
-- | transform conditional expressions
diCondExpr :: ConstrType -> String -> CondExpr -> DI CondExpr
diCondExpr cty fun (CondExpr p e1 e2) = 
  liftM2 (CondExpr p) (diExpr cty fun e1) (diExpr cty fun e2)
  
-- | transform left hand sides
diLhs :: ConstrType -> String -> Lhs -> DI Lhs
diLhs cty fun (FunLhs id0 ps) = 
  return $ FunLhs id0 (dictParams ++ ps)  
  where 
  dictParams = map (VariablePattern . contextElemToVar fun) (fst cty)
diLhs cty fun (OpLhs p1 id0 p2) = diLhs cty fun (FunLhs id0 [p1, p2])
diLhs cty fun a@(ApLhs _ _) =
  let (f, ps) = flatLhs a
  in diLhs cty fun (FunLhs f ps)  

-- | transform expressions
diExpr :: ConstrType -> String -> Expression -> DI Expression
diExpr _cty _fun e = return e -- TODO


-- |generates an identifier for the given function and context element
contextElemToVar:: String -> (QualIdent, Type) -> Ident
contextElemToVar fun (cls, ty) =
  -- TODO: better name generation?
  flip renameIdent 1 $ mkIdent (fun ++ sep ++ show cls ++ sep ++ show ty)


-- ---------------------------------------------------------------------------
-- helper functions
-- ---------------------------------------------------------------------------

type ConstrType = (BT.Context, Type)

mirrorCx :: Context_ -> BT.Context
mirrorCx cx = map (\(qid, ty) -> (qid, mirrorTy ty)) cx

mirrorTy :: Type_ -> Type
mirrorTy (TypeVariable_ n) = TypeVariable n
mirrorTy (TypeConstructor_ q tys) = TypeConstructor q (map mirrorTy tys)
mirrorTy (TypeArrow_ t1 t2) = TypeArrow (mirrorTy t1) (mirrorTy t2)
mirrorTy (TypeConstrained_ tys n) = TypeConstrained (map mirrorTy tys) n
mirrorTy (TypeSkolem_ n) = TypeSkolem n
mirrorTy (TypeRecord_ tys n) = TypeRecord (map (\(id0, ty) -> (id0, mirrorTy ty)) tys) n

mirrorCT :: ConstrType_ -> ConstrType
mirrorCT (cx, ty) = (mirrorCx cx, mirrorTy ty)
