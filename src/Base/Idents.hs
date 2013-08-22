{- |
    Module      :  $Header$
    Description :  Identifiers
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
    
    This file contains some identifiers used in different places, mainly *before*
    the qualification stage. As these identifiers are later expanded, they 
    must be provided in the value environment; currently they are provided under
    a dummy module name. 
-}

module Base.Idents where

import Curry.Base.Ident
import Base.Names
import Curry.Syntax

eqClsIdentName :: String
eqClsIdentName = "Eq"

ordClsIdentName :: String
ordClsIdentName = "Ord"

showClsIdentName :: String
showClsIdentName = "Show"

readClsIdentName :: String
readClsIdentName = "Read"

boundedClsIdentName :: String
boundedClsIdentName = "Bounded"

enumClsIdentName :: String
enumClsIdentName = "Enum"

mkTCPQIdent :: String -> QualIdent
mkTCPQIdent = qualifyWith tcPreludeMIdent . mkIdent

eqClsIdent :: QualIdent
eqClsIdent = mkTCPQIdent eqClsIdentName 

ordClsIdent :: QualIdent
ordClsIdent = mkTCPQIdent ordClsIdentName

showClsIdent :: QualIdent
showClsIdent = mkTCPQIdent showClsIdentName

readClsIdent :: QualIdent
readClsIdent = mkTCPQIdent readClsIdentName

boundedClsIdent :: QualIdent
boundedClsIdent = mkTCPQIdent boundedClsIdentName

enumClsIdent :: QualIdent
enumClsIdent = mkTCPQIdent enumClsIdentName

eqOp :: Ident
eqOp = mkIdent "=="

leqOp :: Ident
leqOp = mkIdent "<="

lessOp :: Ident
lessOp = mkIdent "<"

andOp :: Ident
andOp = mkIdent "&&"

orOp :: Ident
orOp = mkIdent "||"

pointOp :: Ident
pointOp = mkIdent "."

infixEqOp :: InfixOp
infixEqOp = InfixOp Nothing $ qualifyWith tcDummyMIdent $ eqOp

infixLeqOp :: InfixOp
infixLeqOp = InfixOp Nothing $ qualifyWith tcDummyMIdent $ leqOp

infixLessOp :: InfixOp
infixLessOp = InfixOp Nothing $ qualifyWith tcDummyMIdent $ lessOp

infixAndOp :: InfixOp
infixAndOp = InfixOp Nothing $ qualifyWith dummyMIdent $ andOp

infixOrOp :: InfixOp
infixOrOp = InfixOp Nothing $ qualifyWith dummyMIdent $ orOp

infixPointOp :: InfixOp
infixPointOp = InfixOp Nothing $ qualifyWith dummyMIdent $ pointOp

trueCons :: QualIdent
trueCons = qualifyWith dummyMIdent $ mkIdent "True"

falseCons :: QualIdent
falseCons = qualifyWith dummyMIdent $ mkIdent "False"

flipIdent :: Ident
flipIdent = mkIdent "flip"

flipQIdent :: QualIdent
flipQIdent = qualifyWith dummyMIdent flipIdent

otherwiseIdent :: Ident
otherwiseIdent = mkIdent "otherwise"

otherwiseQIdent :: QualIdent
otherwiseQIdent = qualifyWith dummyMIdent $ otherwiseIdent

errorIdent :: Ident
errorIdent = mkIdent "error"

errorQIdent :: QualIdent
errorQIdent = qualifyWith dummyMIdent $ errorIdent 

minBoundIdent :: Ident
minBoundIdent = mkIdent "minBound"

maxBoundIdent :: Ident
maxBoundIdent = mkIdent "maxBound"

minBoundQIdent :: QualIdent
minBoundQIdent = qualifyWith tcDummyMIdent $ minBoundIdent

maxBoundQIdent :: QualIdent
maxBoundQIdent = qualifyWith tcDummyMIdent $ maxBoundIdent

mapIdent :: Ident
mapIdent = mkIdent "map"

mapQIdent :: QualIdent
mapQIdent = qualifyWith dummyMIdent $ mapIdent

toEnumIdent :: Ident
toEnumIdent = mkIdent "toEnum"

fromEnumIdent :: Ident
fromEnumIdent = mkIdent "fromEnum"

toEnumQIdent :: QualIdent
toEnumQIdent = qualifyWith tcDummyMIdent $ toEnumIdent

fromEnumQIdent :: QualIdent
fromEnumQIdent = qualifyWith tcDummyMIdent $ fromEnumIdent

preludeEnumFromToIdent :: Ident
preludeEnumFromToIdent = mkIdent "enumFromTo"

preludeEnumFromToQIdent :: QualIdent
preludeEnumFromToQIdent = qualifyWith dummyMIdent $ preludeEnumFromToIdent

preludeEnumFromThenToIdent :: Ident
preludeEnumFromThenToIdent = mkIdent "enumFromThenTo"

preludeEnumFromThenToQIdent :: QualIdent
preludeEnumFromThenToQIdent = qualifyWith dummyMIdent $ preludeEnumFromThenToIdent
