module Env.Label where

import qualified Data.Map as Map (Map, empty, insertWith)

import Curry.Base.Ident (Ident, QualIdent)

import Base.Types

-- The label environment is used to store information of labels.
-- Unlike usual identifiers like in functions, types etc. identifiers
-- of labels are always represented unqualified. Since the common type
-- environment (type \texttt{ValueEnv}) has some problems with handling
-- imported unqualified identifiers, it is necessary to process the type
-- information for labels seperately.
-- \begin{verbatim}

data LabelInfo = LabelType Ident QualIdent Type deriving Show

type LabelEnv = Map.Map Ident [LabelInfo]

bindLabelType :: Ident -> QualIdent -> Type -> LabelEnv -> LabelEnv
bindLabelType l r ty = Map.insertWith (++) l [LabelType l r ty]

initLabelEnv :: LabelEnv
initLabelEnv = Map.empty
