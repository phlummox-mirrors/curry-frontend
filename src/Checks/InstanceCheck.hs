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
   there are no duplicate instances and that all types specified in a default
   declaration are instances of the Num class.
-}
module Checks.InstanceCheck (instanceCheck) where

import qualified Control.Monad.State as S   (State, execState, gets, modify)
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
import Base.TypeExpansion
import Base.Types
import Base.TypeSubst
import Base.Utils (fst3, snd3, findMultiples)

import Env.Class
import Env.Instance
import Env.TypeConstructor

instanceCheck :: ModuleIdent -> TCEnv -> ClassEnv -> InstEnv -> [Decl a]
              -> (InstEnv, [Message])
instanceCheck m tcEnv clsEnv inEnv ds =
  case findMultiples (local ++ imported) of
    [] -> execINCM (checkDecls tcEnv clsEnv ds) state
    iss -> (inEnv, map (errMultipleInstances tcEnv) iss)
  where
    local = map (flip InstSource m) $ concatMap (genInstIdents m tcEnv) ds
    imported = map (uncurry InstSource) $ map (fmap fst3) $ Map.toList inEnv
    state = INCState m inEnv []

-- In order to provide better error messages, we use the following data type
-- to keep track of an instance's source, i.e., the module it was defined in.

data InstSource = InstSource InstIdent ModuleIdent

instance Eq InstSource where
  InstSource i1 _ == InstSource i2 _ = i1 == i2

-- |Instance Check Monad
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

-- First, the compiler adds all explicit instance declarations to the
-- instance environment.

bindInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
bindInstance tcEnv clsEnv (InstanceDecl _ cx qcls inst ds) = do
  m <- getModuleIdent
  let PredType ps _ = expandPolyType m tcEnv clsEnv $ QualTypeExpr cx inst
  modifyInstEnv $
    bindInstInfo (genInstIdent m tcEnv qcls inst) (m, ps, impls [] ds)
  where impls is [] = is
        impls is (FunctionDecl _ _ f eqs:ds')
          | f' `elem` map fst is = impls is ds'
          | otherwise            = impls ((f', eqnArity $ head eqs) : is) ds'
          where f' = unRenameIdent f
        impls _ _ = internalError "InstanceCheck.bindInstance.impls"
bindInstance _     _      _                                = ok

-- Then, the compiler checks the contexts of all explicit instance
-- declarations to detect missing super class instances. For an instance
-- declaration
--
-- instance cx => C (T u_1 ... u_k) where ...
--
-- the compiler ensures that T is an instance of all of C's super classes
-- and also that the contexts of the corresponding instance declarations are
-- satisfied by cx.

checkDecls :: TCEnv -> ClassEnv -> [Decl a] -> INCM ()
checkDecls tcEnv clsEnv ds = do
  mapM_ (bindInstance tcEnv clsEnv) ids
  mapM_ (checkInstance tcEnv clsEnv) ids
  mapM_ (checkDefault tcEnv clsEnv) dds
  where ids = filter isInstanceDecl ds
        dds = filter isDefaultDecl ds

checkInstance :: TCEnv -> ClassEnv -> Decl a -> INCM ()
checkInstance tcEnv clsEnv (InstanceDecl p cx cls inst _) = do
  m <- getModuleIdent
  let PredType ps ty = expandPolyType m tcEnv clsEnv $ QualTypeExpr cx inst
      ocls = getOrigName m cls tcEnv
      ps' = Set.fromList [ Pred scls ty | scls <- superClasses ocls clsEnv ]
      doc = ppPred m $ Pred cls ty
      what = "instance declaration"
  ps'' <- reducePredSet p what doc tcEnv clsEnv ps'
  Set.mapM_ (report . errMissingInstance m p what doc) $
    ps'' `Set.difference` (maxPredSet clsEnv ps)
checkInstance _ _ _ = ok

-- All types specified in the optional default declaration of a module
-- must be instances of the Num class. Since these types are used to resolve
-- ambiguous type variables, the predicate sets of the respective instances
-- must be empty.

checkDefault :: TCEnv -> ClassEnv -> Decl a -> INCM ()
checkDefault tcEnv clsEnv (DefaultDecl p tys) =
  mapM_ (checkDefaultType p tcEnv clsEnv) tys
checkDefault _ _ _ = ok

checkDefaultType :: Position -> TCEnv -> ClassEnv -> TypeExpr -> INCM ()
checkDefaultType p tcEnv clsEnv ty = do
  m <- getModuleIdent
  let PredType _ ty' = expandPolyType m tcEnv clsEnv $ QualTypeExpr [] ty
  ps <- reducePredSet p what empty tcEnv clsEnv (Set.singleton $ Pred qNumId ty')
  Set.mapM_ (report . errMissingInstance m p what empty) ps
  where what = "default declaration"

-- The function 'reducePredSet' simplifies a predicate set of the form
-- (C_1 tau_1,..,C_n tau_n) where the tau_i are arbitrary types into a
-- predicate set where all predicates are of the form C u with u being
-- a type variable. An error is reported if the predicate set cannot
-- be transformed into this form. In addition, we remove all predicates
-- that are implied by others within the same set.

reducePredSet :: Position -> String -> Doc -> TCEnv -> ClassEnv -> PredSet
              -> INCM PredSet
reducePredSet p what doc tcEnv clsEnv ps = do
  m <- getModuleIdent
  inEnv <- getInstEnv
  let (ps1, ps2) = partitionPredSet $ minPredSet clsEnv $ reducePreds inEnv ps
  Set.mapM_ (report . errMissingInstance m p what doc) ps2
  return ps1
  where
    reducePreds inEnv = Set.concatMap $ reducePred inEnv
    reducePred inEnv predicate = maybe (Set.singleton predicate)
                                       (reducePreds inEnv)
                                       (instPredSet tcEnv inEnv predicate)

instPredSet :: TCEnv -> InstEnv -> Pred -> Maybe PredSet
instPredSet tcEnv inEnv (Pred qcls ty) =
  case unapplyType False ty of
    (TypeConstructor tc, tys) ->
      fmap (expandAliasType tys . snd3) (lookupInstInfo (qcls, tc) inEnv)
    _ -> Nothing

-- ---------------------------------------------------------------------------
-- Auxiliary definitions
-- ---------------------------------------------------------------------------

genInstIdents :: ModuleIdent -> TCEnv -> Decl a -> [InstIdent]
genInstIdents m tcEnv (InstanceDecl _ _ qcls ty _) =
  [genInstIdent m tcEnv qcls ty]
genInstIdents _ _     _                            = []

genInstIdent :: ModuleIdent -> TCEnv -> QualIdent -> TypeExpr -> InstIdent
genInstIdent m tcEnv qcls = qualInstIdent m tcEnv . (,) qcls . typeConstr

-- When qualifiying an instance identifier, we replace both the class and
-- type constructor with their original names as found in the type constructor
-- environment.

qualInstIdent :: ModuleIdent -> TCEnv -> InstIdent -> InstIdent
qualInstIdent m tcEnv (cls, tc) = (qual cls, qual tc)
  where
    qual = flip (getOrigName m) tcEnv

unqualInstIdent :: TCEnv -> InstIdent -> InstIdent
unqualInstIdent tcEnv (qcls, tc) = (unqual qcls, unqual tc)
  where
    unqual = head . flip reverseLookupByOrigName tcEnv

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errMultipleInstances :: TCEnv -> [InstSource] -> Message
errMultipleInstances tcEnv iss = message $
  text "Multiple instances for the same class and type" $+$
    nest 2 (vcat (map ppInstSource iss))
  where
    ppInstSource (InstSource i m) = ppInstIdent (unqualInstIdent tcEnv i) <+>
      parens (text "defined in" <+> ppMIdent m)

errMissingInstance :: ModuleIdent -> Position -> String -> Doc -> Pred
                   -> Message
errMissingInstance m p what doc predicate = posMessage p $ hsep
  [ text "Missing instance for", ppPred m predicate
  , text "in", text what, doc
  ]
