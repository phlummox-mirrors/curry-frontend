{- |
    Module      :  $Header$
    Description :  Environment for record labels
    Copyright   :  (c) 2002-2004, Wolfgang Lux
                       2011, Björn Peemöller   (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The label environment is used to store information of labels.
    Unlike usual identifiers like in functions, types etc. identifiers
    of labels are always represented unqualified. Since the common type
    environment (type \texttt{ValueEnv}) has some problems with handling
    imported unqualified identifiers, it is necessary to process the type
    information for labels seperately.
-}
module Env.Label where

import qualified Data.Map as Map (Map, empty, insertWith)

import Curry.Base.Ident (Ident, QualIdent)

import Base.Types

data LabelInfo = LabelType Ident QualIdent Type deriving Show

type LabelEnv = Map.Map Ident [LabelInfo]

initLabelEnv :: LabelEnv
initLabelEnv = Map.empty

bindLabelType :: Ident -> QualIdent -> Type -> LabelEnv -> LabelEnv
bindLabelType l r ty = Map.insertWith (++) l [LabelType l r ty]
