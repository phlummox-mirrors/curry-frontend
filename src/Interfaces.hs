{- |
    Module      :  $Header$
    Description :  Loading interfaces
    Copyright   :  (c) 2000-2004, Wolfgang Lux
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    The compiler maintains a global environment holding all (directly or
    indirectly) imported interface declarations for a module.

    This module contains a function to load *all* interface declarations
    declared by the (directly or indirectly) imported modules, regardless
    whether they are included by the import specification or not.

    The declarations are later brought into the scope of the module via the
    function importModules (see module @Imports@).

    Interface files are updated by the Curry builder when necessary
    (see module @CurryBuilder@).
-}
module Interfaces (loadInterfaces) where

import Control.Monad (foldM, liftM, unless)
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map as Map

import Curry.Base.Ident
import Curry.Base.Position
import qualified Curry.ExtendedFlat.Type as EF
import Curry.Files.PathUtils as PU
import Curry.Syntax

import Base.Messages (Message, toMessage, errorMessage, internalError)

import Env.Interface

-- TODO: Propagate errors

-- |Load the interface files into the 'InterfaceEnv'
loadInterfaces :: [FilePath] -> Module -> IO InterfaceEnv
loadInterfaces paths (Module m _ is _) =
  foldM (loadInterface paths [m]) initInterfaceEnv
        [(p, m') | ImportDecl p m' _ _ _ <- is]

-- |Load an interface into the environment
--
-- If an import declaration for a module is found, the compiler first
-- checks whether an import for the module is already pending. In this
-- case the module imports are cyclic which is not allowed in Curry. The
-- compilation will therefore be aborted. Next, the compiler checks
-- whether the module has already been imported. If so, nothing needs to
-- be done, otherwise the interface will be searched for in the import paths
-- and compiled.
loadInterface :: [FilePath] -> [ModuleIdent] -> InterfaceEnv
              -> (Position, ModuleIdent) -> IO InterfaceEnv
loadInterface paths ctxt mEnv (p, m)
  | m `elem` ctxt       = errorMessage $ errCyclicImport p
                        $ m : takeWhile (/= m) ctxt
  | m `Map.member` mEnv = return mEnv
  | otherwise           = PU.lookupInterface paths m >>=
      maybe (errorMessage $ errInterfaceNotFound p m)
            (compileInterface paths ctxt mEnv m)

-- |Compile an interface by recursively loading its dependencies
--
-- After reading an interface, all imported interfaces are recursively
-- loaded and entered into the interface's environment. There is no need
-- to check FlatCurry-Interfaces, since these files contain automatically
-- generated FlatCurry terms (type \texttt{Prog}).
compileInterface :: [FilePath] -> [ModuleIdent] -> InterfaceEnv
                 -> ModuleIdent -> FilePath -> IO InterfaceEnv
compileInterface paths ctxt mEnv m fn = do
  mintf <- (fmap flatToCurryInterface) `liftM` EF.readFlatInterface fn
  case mintf of
    Nothing -> errorMessage $ errInterfaceNotFound (first fn) m
    Just intf@(Interface m' is _) -> do
      unless (m' == m) $ errorMessage $ errWrongInterface (first fn) m m'
      let importDecls = [ (pos, imp) | IImportDecl pos imp <- is ]
      mEnv' <- foldM (loadInterface paths (m : ctxt)) mEnv importDecls
      return $ Map.insert m intf mEnv'

-- |Transforms an interface of type 'FlatCurry.Prog' to a Curry interface
-- of type 'CurrySyntax.Interface'. This is necessary to process
-- FlatInterfaces instead of ".icurry" files when using cymake as a frontend
-- for PAKCS.
flatToCurryInterface :: EF.Prog -> Interface
flatToCurryInterface (EF.Prog m imps ts fs os)
  = Interface (fromModuleName m) (map genIImportDecl imps) $ concat
    [ map genITypeDecl $ filter (not . isSpecialPreludeType) ts
    , map genIFuncDecl fs
    , map genIOpDecl os
    ]
  where
  pos = first m

  genIImportDecl :: String -> IImportDecl
  genIImportDecl = IImportDecl pos . fromModuleName

  genITypeDecl :: EF.TypeDecl -> IDecl
  genITypeDecl (EF.Type qn _ is cs)
    | recordExt `isPrefixOf` EF.localName qn
    = ITypeDecl pos
        (genQualIdent qn)
        (map genVarIndexIdent is)
        (RecordType (map genLabeledType cs) Nothing)
    | otherwise
    = IDataDecl pos
        (genQualIdent qn)
        (map genVarIndexIdent is)
        (map (Just . genConstrDecl) cs)
  genITypeDecl (EF.TypeSyn qn _ is t)
    = ITypeDecl pos
        (genQualIdent qn)
        (map genVarIndexIdent is)
        (genTypeExpr t)

  genLabeledType :: EF.ConsDecl -> ([Ident], TypeExpr)
  genLabeledType (EF.Cons qn _ _ [t])
    = ( [renameLabel $ fromLabelExtId $ mkIdent $ EF.localName qn]
      , genTypeExpr t)
  genLabeledType _ = internalError
    "Interfaces.genLabeledType: not exactly one type expression"

  genConstrDecl :: EF.ConsDecl -> ConstrDecl
  genConstrDecl (EF.Cons qn _ _ ts1)
    = ConstrDecl pos [] (mkIdent (EF.localName qn)) (map genTypeExpr ts1)

  genIFuncDecl :: EF.FuncDecl -> IDecl
  genIFuncDecl (EF.Func qn a _ t _)
    = IFunctionDecl pos (genQualIdent qn) a (genTypeExpr t)

  genIOpDecl :: EF.OpDecl -> IDecl
  genIOpDecl (EF.Op qn f p) = IInfixDecl pos (genInfix f) p (genQualIdent qn)

  genTypeExpr :: EF.TypeExpr -> TypeExpr
  genTypeExpr (EF.TVar i)
    = VariableType (genVarIndexIdent i)
  genTypeExpr (EF.FuncType t1 t2)
    = ArrowType (genTypeExpr t1) (genTypeExpr t2)
  genTypeExpr (EF.TCons qn ts1)
    = ConstructorType (genQualIdent qn) (map genTypeExpr ts1)

  genInfix :: EF.Fixity -> Infix
  genInfix EF.InfixOp  = Infix
  genInfix EF.InfixlOp = InfixL
  genInfix EF.InfixrOp = InfixR

  genQualIdent :: EF.QName -> QualIdent
  genQualIdent EF.QName { EF.modName = mdl, EF.localName = lname } =
    qualifyWith (fromModuleName mdl) (mkIdent lname)

  genVarIndexIdent :: Int -> Ident
  genVarIndexIdent i = mkIdent $ 'a' : show i

  isSpecialPreludeType :: EF.TypeDecl -> Bool
  isSpecialPreludeType (EF.Type qn _ _ _)
    = (lname == "[]" || lname == "()") && mdl == "Prelude"
      where EF.QName { EF.modName = mdl, EF.localName = lname} = qn
  isSpecialPreludeType _ = False

errInterfaceNotFound :: Position -> ModuleIdent -> Message
errInterfaceNotFound p m = toMessage p $
  "Interface for module " ++ moduleName m ++ " not found"

errWrongInterface :: Position -> ModuleIdent -> ModuleIdent -> Message
errWrongInterface p m m' = toMessage p $
  "Expected interface for " ++ show m ++ " but found " ++ show m'
  ++ show (moduleQualifiers m, moduleQualifiers m')

errCyclicImport :: Position -> [ModuleIdent] -> Message
errCyclicImport _ []  = internalError "Interfaces.errCyclicImport: empty list"
errCyclicImport p [m] = toMessage p $
  "Recursive import for module " ++ moduleName m
errCyclicImport p ms  = toMessage p $
  "Cylic import dependency between modules "
  ++ intercalate ", " inits ++ " and " ++ lastm
  where
  (inits, lastm)         = splitLast $ map moduleName ms
  splitLast []           = internalError "Interfaces.splitLast: empty list"
  splitLast (x : [])     = ([]  , x)
  splitLast (x : y : ys) = (x : xs, z) where (xs, z) = splitLast (y : ys)
