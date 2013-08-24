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

infixEqOp :: InfixOp
infixEqOp = InfixOp Nothing $ tcPreludeIdent eqOp

infixLeqOp :: InfixOp
infixLeqOp = InfixOp Nothing $ tcPreludeIdent leqOp

infixLessOp :: InfixOp
infixLessOp = InfixOp Nothing $ tcPreludeIdent lessOp

infixGreaterOp :: InfixOp
infixGreaterOp = InfixOp Nothing $ tcPreludeIdent greaterOp

infixAndOp :: InfixOp
infixAndOp = InfixOp Nothing $ preludeIdent andOp

infixOrOp :: InfixOp
infixOrOp = InfixOp Nothing $ preludeIdent orOp

infixPointOp :: InfixOp
infixPointOp = InfixOp Nothing $ preludeIdent pointOp

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

 

