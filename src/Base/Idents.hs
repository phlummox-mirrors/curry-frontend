{- |
    Module      :  $Header$
    Description :  Identifiers
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable
    
    This file contains some identifiers used in different places. 
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

infixEqOp :: InfixOp
infixEqOp = InfixOp Nothing $ qualifyWith dummyMIdent $ eqOp

infixLeqOp :: InfixOp
infixLeqOp = InfixOp Nothing $ qualifyWith dummyMIdent $ leqOp

infixLessOp :: InfixOp
infixLessOp = InfixOp Nothing $ qualifyWith dummyMIdent $ lessOp

infixAndOp :: InfixOp
infixAndOp = InfixOp Nothing $ qualifyWith dummyMIdent $ andOp

infixOrOp :: InfixOp
infixOrOp = InfixOp Nothing $ qualifyWith dummyMIdent $ orOp

trueCons :: QualIdent
trueCons = qualifyWith dummyMIdent $ mkIdent "True"

falseCons :: QualIdent
falseCons = qualifyWith dummyMIdent $ mkIdent "False"

flipIdent :: Ident
flipIdent = mkIdent "flip"

errorIdent :: Ident
errorIdent = mkIdent "error"

errorQIdent :: QualIdent
errorQIdent = qualifyWith dummyMIdent $ errorIdent 