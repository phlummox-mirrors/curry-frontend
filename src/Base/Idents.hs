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

numClsIdentName :: String
numClsIdentName = "Num"

fractionalClsIdentName :: String
fractionalClsIdentName = "Fractional"

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

numClsIdent :: QualIdent
numClsIdent = mkTCPQIdent numClsIdentName

fractionalClsIdent :: QualIdent
fractionalClsIdent = mkTCPQIdent fractionalClsIdentName

-- ---------------------------------------------------------------------------

preludeIdent :: Ident -> QualIdent
preludeIdent = qualifyWith dummyMIdent

tcPreludeIdent :: Ident -> QualIdent
tcPreludeIdent = qualifyWith tcDummyMIdent

-- ---------------------------------------------------------------------------

eqOp :: Ident
eqOp = mkIdent "=="

leqOp :: Ident
leqOp = mkIdent "<="

lessOp :: Ident
lessOp = mkIdent "<"

greaterOp :: Ident
greaterOp = mkIdent ">"

andOp :: Ident
andOp = mkIdent "&&"

orOp :: Ident
orOp = mkIdent "||"

pointOp :: Ident
pointOp = mkIdent "."

eqInfixOp :: InfixOp
eqInfixOp = InfixOp Nothing $ tcPreludeIdent eqOp

leqInfixOp :: InfixOp
leqInfixOp = InfixOp Nothing $ tcPreludeIdent leqOp

lessInfixOp :: InfixOp
lessInfixOp = InfixOp Nothing $ tcPreludeIdent lessOp

greaterInfixOp :: InfixOp
greaterInfixOp = InfixOp Nothing $ tcPreludeIdent greaterOp

andInfixOp :: InfixOp
andInfixOp = InfixOp Nothing $ preludeIdent andOp

orInfixOp :: InfixOp
orInfixOp = InfixOp Nothing $ preludeIdent orOp

pointInfixOp :: InfixOp
pointInfixOp = InfixOp Nothing $ preludeIdent pointOp

-- ---------------------------------------------------------------------------

trueCons :: QualIdent
trueCons = preludeIdent $ mkIdent "True"

falseCons :: QualIdent
falseCons = preludeIdent $ mkIdent "False"

flipIdent :: Ident
flipIdent = mkIdent "flip"

flipQIdent :: QualIdent
flipQIdent = preludeIdent flipIdent

otherwiseIdent :: Ident
otherwiseIdent = mkIdent "otherwise"

otherwiseQIdent :: QualIdent
otherwiseQIdent = preludeIdent otherwiseIdent

errorIdent :: Ident
errorIdent = mkIdent "error"

errorQIdent :: QualIdent
errorQIdent = preludeIdent errorIdent 

minBoundIdent :: Ident
minBoundIdent = mkIdent "minBound"

maxBoundIdent :: Ident
maxBoundIdent = mkIdent "maxBound"

minBoundQIdent :: QualIdent
minBoundQIdent = tcPreludeIdent minBoundIdent

maxBoundQIdent :: QualIdent
maxBoundQIdent = tcPreludeIdent maxBoundIdent

mapIdent :: Ident
mapIdent = mkIdent "map"

mapQIdent :: QualIdent
mapQIdent = preludeIdent mapIdent

toEnumIdent :: Ident
toEnumIdent = mkIdent "toEnum"

fromEnumIdent :: Ident
fromEnumIdent = mkIdent "fromEnum"

toEnumQIdent :: QualIdent
toEnumQIdent = tcPreludeIdent toEnumIdent

fromEnumQIdent :: QualIdent
fromEnumQIdent = tcPreludeIdent fromEnumIdent

preludeEnumFromToIdent :: Ident
preludeEnumFromToIdent = mkIdent "enumFromTo"

preludeEnumFromToQIdent :: QualIdent
preludeEnumFromToQIdent = preludeIdent preludeEnumFromToIdent

preludeEnumFromThenToIdent :: Ident
preludeEnumFromThenToIdent = mkIdent "enumFromThenTo"

preludeEnumFromThenToQIdent :: QualIdent
preludeEnumFromThenToQIdent = preludeIdent preludeEnumFromThenToIdent

showStringIdent :: Ident
showStringIdent = mkIdent "showString"

showParenIdent :: Ident
showParenIdent = mkIdent "showParen"

showsPrecIdent :: Ident
showsPrecIdent = mkIdent "showsPrec"

showStringQIdent :: QualIdent
showStringQIdent = tcPreludeIdent showStringIdent

showParenQIdent :: QualIdent
showParenQIdent = tcPreludeIdent showParenIdent

showsPrecQIdent :: QualIdent
showsPrecQIdent = tcPreludeIdent showsPrecIdent



tcPreludeEnumFromIdent :: Ident
tcPreludeEnumFromIdent = mkIdent "enumFrom"

tcPreludeEnumFromQIdent :: QualIdent
tcPreludeEnumFromQIdent = tcPreludeIdent tcPreludeEnumFromIdent

tcPreludeEnumFromThenIdent :: Ident
tcPreludeEnumFromThenIdent = mkIdent "enumFromThen"

tcPreludeEnumFromThenQIdent :: QualIdent
tcPreludeEnumFromThenQIdent = tcPreludeIdent tcPreludeEnumFromThenIdent

tcPreludeEnumFromToIdent :: Ident
tcPreludeEnumFromToIdent = mkIdent "enumFromTo"

tcPreludeEnumFromToQIdent :: QualIdent
tcPreludeEnumFromToQIdent = tcPreludeIdent tcPreludeEnumFromToIdent

tcPreludeEnumFromThenToIdent :: Ident
tcPreludeEnumFromThenToIdent = mkIdent "enumFromThenTo"

tcPreludeEnumFromThenToQIdent :: QualIdent
tcPreludeEnumFromThenToQIdent = tcPreludeIdent tcPreludeEnumFromThenToIdent


fromIntegerIdent :: Ident
fromIntegerIdent = mkIdent "fromInteger"

fromFloatIdent :: Ident
fromFloatIdent = mkIdent "fromFloat"

fromIntegerQIdent :: QualIdent
fromIntegerQIdent = tcPreludeIdent fromIntegerIdent

fromFloatQIdent :: QualIdent
fromFloatQIdent = tcPreludeIdent fromFloatIdent

negateIdent :: Ident
negateIdent = mkIdent "negate"

negateQIdent :: QualIdent
negateQIdent = tcPreludeIdent negateIdent
