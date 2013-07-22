{- |
    Module      :  $Header$
    Description :  
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Transforms the export specification: Exports of classes are transformed
    into exports of the corresponding elements used for implementing the 
    type classes, i.e., the type of a class and the selector functions. 

-}

module Transformations.ExportSpec (transExportSpec) where

import CompilerEnv
{-
import Env.ClassEnv
import Env.Value
-}
import Curry.Syntax.Type
{-
import Base.Utils
import Curry.Base.Ident

import Control.Monad.State as S
-}

-- ----------------------------------------------------------------------------
-- the state monad used
-- ----------------------------------------------------------------------------
{-
type ES = S.State ESState

data ESState = ESState 
  { theClassEnv :: ClassEnv
  -- , theValueEnv :: ValueEnv
  }

initState :: ClassEnv -> ValueEnv -> ESState
initState cEnv _vEnv = ESState cEnv {-vEnv-} 

runES :: ES a -> ESState -> a
runES comp init0 = let (a, _s) = S.runState comp init0 in a

getClassEnv :: ES ClassEnv
getClassEnv = S.gets theClassEnv
-}
-- getValueEnv :: ES ValueEnv
-- getValueEnv = S.gets theValueEnv

-- ----------------------------------------------------------------------------


transExportSpec :: CompilerEnv -> Module -> Module
transExportSpec _cEnv mdl = mdl
  -- runES (transExportSpec' mdl) (initState (classEnv cEnv) (valueEnv cEnv))
{-
transExportSpec' :: Module -> ES Module
transExportSpec' mdl@(Module _ Nothing _ _)     = return mdl
transExportSpec'     (Module m (Just es) is ds) = do
  es' <- transExportSpec'' es
  return $ Module m (Just es') is ds
  

transExportSpec'' :: ExportSpec -> ES ExportSpec
transExportSpec'' (Exporting p es) = 
  Exporting p `liftM` (concatMapM transExport es)

transExport :: Export -> ES [Export]
transExport e@(Export qid) = handleClassExport qid e
transExport e@(ExportTypeWith qid _) = handleClassExport qid e
transExport e@(ExportTypeAll qid) = handleClassExport qid e
transExport mdl@(ExportModule _) = return [mdl]

handleClassExport :: QualIdent -> Export -> ES [Export]
handleClassExport qid orig = do
  cEnv <- getClassEnv
  case lookupClass cEnv qid of
    Nothing -> return [orig]
    Just _ -> return [] -- TODO!

-}