module Transformations where

import Curry.Syntax

import Base.Types

import Transform.CaseCompletion as CC (completeCase)
import Transform.CurryToIL as CTIL (ilTrans, translType)
import Transform.Desugar as DS (desugar)
import Transform.Lift as L (lift)
import Transform.Qual as Q (qual)
import Transform.Simplify as S (simplify)

import CompilerEnv
import qualified IL

completeCase :: IL.Module -> CompilerEnv -> (IL.Module, CompilerEnv)
completeCase mdl env = (CC.completeCase (moduleEnv env) mdl, env)

ilTrans :: Bool -> Module -> CompilerEnv -> (IL.Module, CompilerEnv)
ilTrans flat mdl env = (il, env)
  where il = CTIL.ilTrans flat (valueEnv env) (tyConsEnv env) (evalAnnotEnv env) mdl

translType :: Type -> IL.Type
translType = CTIL.translType

desugar :: Module -> CompilerEnv -> (Module, CompilerEnv)
desugar mdl env = (mdl', env { valueEnv = tyEnv' })
  where (mdl', tyEnv') = DS.desugar (valueEnv env) (tyConsEnv env) mdl

lift :: Module -> CompilerEnv -> (Module, CompilerEnv)
lift mdl env = (mdl', env { valueEnv = tyEnv', evalAnnotEnv = eEnv' })
  where (mdl', tyEnv', eEnv') = L.lift (valueEnv env) (evalAnnotEnv env) mdl

qual :: [Decl] -> CompilerEnv -> ([Decl], CompilerEnv)
qual decls env = (decls', env)
  where decls' = Q.qual (moduleIdent env) (valueEnv env) decls

simplify :: Bool -> Module -> CompilerEnv -> (Module, CompilerEnv)
simplify flat mdl env = (mdl', env { valueEnv = tyEnv' })
  where (mdl', tyEnv') = S.simplify flat (valueEnv env) (evalAnnotEnv env) mdl
