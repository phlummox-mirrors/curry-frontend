{- |
    Module      :  $Header$
    Description :  Checks instances
    Copyright   :  (c)        2016 Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Before type checking, the compiler checks for every instance declaration
   that all necessary super class instances exist. It is also checked that
   there are no duplicate instance declarations.
-}
module Checks.InstanceCheck (instanceCheck) where

import qualified Control.Monad.State as S (State, execState, gets, modify)
import qualified Data.Map            as Map
import qualified Data.Set.Extra      as Set

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax
import Curry.Syntax.Pretty

import Base.CurryTypes
import Base.Messages (Message, posMessage, message, internalError)
import Base.TopEnv
import Base.Types
import Base.Utils (findMultiples)

import Env.InstEnv
import Env.TypeConstructor

instanceCheck :: ModuleIdent -> TCEnv -> InstEnv -> [Decl]
              -> (InstEnv, [Message])
instanceCheck m tcEnv inEnv ds =
  case findMultiples (local ++ imported) of
    [] -> execINCM (checkDecls tcEnv ds) state
    iss -> (inEnv, map (errMultipleInstances . map (unqualInstIdent tcEnv)) iss)
  where
    local = concatMap (genInstIdents tcEnv) ds
    imported = Map.keys inEnv
    state = INCState m inEnv []

-- Instance Check Monad
type INCM = S.State INCState

-- |Internal state of the Instance Check
data INCState = INCState
  { moduleIdent :: ModuleIdent
  , instEnv     :: InstEnv
  , errors      :: [Message]
  }

execINCM :: INCM a -> INCState -> (InstEnv, [Message])
execINCM incm s =
  let s' = S.execState incm s in (instEnv s', reverse $ errors s')

getModuleIdent :: INCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getInstEnv :: INCM InstEnv
getInstEnv = S.gets instEnv

modifyInstEnv :: (InstEnv -> InstEnv) -> INCM ()
modifyInstEnv f = S.modify $ \s -> s { instEnv = f $ instEnv s }

report :: Message -> INCM ()
report err = S.modify (\s -> s { errors = err : errors s })

ok :: INCM ()
ok = return ()

checkDecls :: TCEnv -> [Decl] -> INCM ()
checkDecls tcEnv ds = do
  mapM_ (bindInstance tcEnv) ds
  --TODO: bind derived instances
  mapM_ (checkDecl tcEnv) ds

bindInstance :: TCEnv -> Decl -> INCM ()
bindInstance tcEnv (InstanceDecl _ cx qcls inst ds) = do
  m <- getModuleIdent
  modifyInstEnv $
    bindInstInfo (genInstIdent tcEnv qcls inst) (m, toPredSet [] cx)
bindInstance _     _                                = ok

checkDecl :: TCEnv -> Decl -> INCM ()
checkDecl tcEnv (InstanceDecl pos cx qcls inst _) = do
  ps'' <- reducePredSet pos tcEnv ps'
  Set.mapM_ (report . errMissingInstance pos) $
    ps'' `Set.difference` (maxPredSet tcEnv ps)
  where
    PredType ps ty = toPredType [] $ QualTypeExpr cx inst
    ps' = Set.fromList [Pred qcls' ty | qcls' <- superClasses qcls tcEnv]
checkDecl _ _ = ok

reducePredSet :: Position -> TCEnv -> PredSet -> INCM PredSet
reducePredSet pos tcEnv ps = do
  inEnv <- getInstEnv
  let (ps1, ps2) = partitionPredSet $ minPredSet tcEnv $ reducePreds inEnv ps
  Set.mapM_ (report . errMissingInstance pos) ps2
  return ps1
  where
    reducePreds inEnv = Set.concatMap $ reducePred inEnv
    reducePred inEnv p@(Pred qcls ty) =
      case lookupInstInfo (genInstIdent tcEnv qcls $ fromType ty) inEnv of
       Just (_, ps) -> reducePreds inEnv ps
       _ -> Set.singleton p

--TODO: check derived instances

-- ---------------------------------------------------------------------------
-- Miscellaneous functions
-- ---------------------------------------------------------------------------

minPredSet :: TCEnv -> PredSet -> PredSet
minPredSet tcEnv ps =
  ps `Set.difference` Set.concatMap implied ps
  where
    implied (Pred qcls ty) =
      Set.fromList [Pred qcls' ty | qcls' <- tail (allSuperClasses qcls tcEnv)]

maxPredSet :: TCEnv -> PredSet -> PredSet
maxPredSet tcEnv ps = Set.concatMap implied ps
  where
    implied (Pred qcls ty) =
      Set.fromList [Pred qcls' ty | qcls' <- allSuperClasses qcls tcEnv]

partitionPredSet :: PredSet -> (PredSet, PredSet)
partitionPredSet = Set.partition $ \(Pred _ ty) -> isTypeVariable ty
  where
    --TODO: check if TypeApply has to be considered
    isTypeVariable (TypeVariable _) = True
    isTypeVariable _                = False

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

genInstIdents :: TCEnv -> Decl -> [InstIdent]
--TODO: add derived instances from data type and newtype declarations
genInstIdents tcEnv (InstanceDecl _ _ qcls ty _) = [genInstIdent tcEnv qcls ty]
genInstIdents _     _                            = []

genInstIdent :: TCEnv -> QualIdent -> TypeExpr -> InstIdent
genInstIdent tcEnv qcls = qualInstIdent tcEnv . (,) qcls . typeConstr

originalName :: TCEnv -> QualIdent -> QualIdent
originalName tcEnv = origName . head . flip qualLookupTypeInfo tcEnv

qualInstIdent :: TCEnv -> InstIdent -> InstIdent
qualInstIdent tcEnv (cls, tc) = (originalName tcEnv cls, originalName tcEnv tc)

unqualInstIdent :: TCEnv -> InstIdent -> InstIdent
unqualInstIdent tcEnv (qcls, tc) = (unqual qcls, unqual tc)
  where
    unqual x = case lookupTypeInfo x' tcEnv of
                 [y] | origName y == x -> qualify x'
                 _ -> x
      where
        x' = unqualify x

typeConstr :: TypeExpr -> QualIdent
typeConstr (ConstructorType   tc) = tc
typeConstr (ApplyType       ty _) = typeConstr ty
typeConstr (VariableType       _) = internalError
  "Checks.InstanceCheck.typeConstr: variable type"
typeConstr (TupleType        tys) = qTupleId (length tys)
typeConstr (ListType           _) = qListId
typeConstr (ArrowType        _ _) = qArrowId
typeConstr (ParenType         ty) = typeConstr ty

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleInstances :: [InstIdent] -> Message
errMultipleInstances [] = internalError
  "Checks.InstanceCheck.errMultipleInstances: empty list"
errMultipleInstances is = message $
  text "Multiple instances for the same class and type" $+$
    nest 2 (vcat (map ppInstIdent is))
  where
    ppInstIdent (qcls, qtc) = ppQIdent qcls <+> ppQIdent qtc

errMissingInstance :: Position -> Pred -> Message
errMissingInstance pos p = posMessage pos $ hsep
  [ text "Missing instance for", ppPred p, text "in instance declaration" ]
