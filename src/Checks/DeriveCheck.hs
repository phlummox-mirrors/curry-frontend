{- |
    Module      :  $Header$
    Description :  Checks deriving clauses
    Copyright   :  (c)        2016 Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   Before entering derived instances into the instance environment, the
   compiler has to ensure that it is not asked for other instances than
   those of supported type classes.
-}
module Checks.DeriveCheck (deriveCheck) where

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Messages (Message, posMessage)

import Env.TypeConstructor

deriveCheck :: TCEnv -> Module a -> [Message]
deriveCheck tcEnv (Module _ m _ _ ds) = concatMap (checkDecl m tcEnv) ds

-- No instances can be derived for abstract data types as well as for
-- existential data types.

checkDecl :: ModuleIdent -> TCEnv -> Decl a -> [Message]
checkDecl m tcEnv (DataDecl   _ tc _ cs clss)
  | null clss                       = []
  | null cs                         = [errNoAbstractDerive tc]
  | any (not . null . existVars) cs = [errNoExistentialDerive tc]
  | otherwise                       = concatMap (checkDerivable m tcEnv cs) clss
checkDecl m tcEnv (NewtypeDecl _ _ _ nc clss) =
  concatMap (checkDerivable m tcEnv [toConstrDecl nc]) clss
checkDecl _ _     _                           = []

checkDerivable :: ModuleIdent -> TCEnv -> [ConstrDecl] -> QualIdent -> [Message]
checkDerivable m tcEnv cs cls
  | ocls == qEnumId && not (isEnum cs)       = [errNotEnum cls]
  | ocls == qBoundedId && not (isBounded cs) = [errNotBounded cls]
  | ocls `notElem` derivableClasses          = [errNotDerivable ocls]
  | otherwise                                = []
  where ocls = getOrigName m cls tcEnv

derivableClasses :: [QualIdent]
derivableClasses = [qEqId, qOrdId, qEnumId, qBoundedId, qReadId, qShowId]

-- Instances of 'Enum' can be derived only for enumeration types, i.e., types
-- where all data constructors are constants.

isEnum :: [ConstrDecl] -> Bool
isEnum cs = all ((0 ==) . constrArity) cs

-- Instances of 'Bounded' can be derived only for enumerations and for single
-- constructor types.

isBounded :: [ConstrDecl] -> Bool
isBounded cs = length cs == 1 || isEnum cs

-- ---------------------------------------------------------------------------
-- Auxiliary functions
-- ---------------------------------------------------------------------------

toConstrDecl :: NewConstrDecl -> ConstrDecl
toConstrDecl (NewConstrDecl p c      ty) = ConstrDecl p [] [] c [ty]
toConstrDecl (NewRecordDecl p c (l, ty)) =
  RecordDecl p [] [] c [FieldDecl p [l] ty]

constrArity :: ConstrDecl -> Int
constrArity (ConstrDecl  _ _ _ _ tys) = length tys
constrArity (ConOpDecl   _ _ _ _ _ _) = 2
constrArity c@(RecordDecl  _ _ _ _ _) = length $ recordLabels c

existVars :: ConstrDecl -> [Ident]
existVars (ConstrDecl _ evs _ _ _  ) = evs
existVars (ConOpDecl  _ evs _ _ _ _) = evs
existVars (RecordDecl _ evs _ _ _  ) = evs

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errNoAbstractDerive :: HasPosition a => a -> Message
errNoAbstractDerive p = posMessage p $
  text "Instances cannot be derived for abstract data types"

errNoExistentialDerive :: HasPosition a => a -> Message
errNoExistentialDerive p = posMessage p $
  text "Instances cannot be derived for existential data types"

errNotDerivable :: QualIdent -> Message
errNotDerivable cls = posMessage cls $ hsep $ map text
  ["Instances of type class", escQualName cls, "cannot be derived"]

errNotEnum :: HasPosition a => a -> Message
errNotEnum p = posMessage p $
  text "Instances for Enum can be derived only for enumeration types"

errNotBounded :: HasPosition a => a -> Message
errNotBounded p = posMessage p $
  text "Instances of Bounded can be derived only for enumeration" <+>
  text "and single constructor types"