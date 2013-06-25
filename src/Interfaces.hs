{- |
    Module      :  $Header$
    Description :  Loading interfaces
    Copyright   :  (c) 2000 - 2004, Wolfgang Lux
                       2011       , Björn Peemöller
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
    function 'importModules' (see module @Imports@).

    Interface files are updated by the Curry builder when necessary
    (see module @CurryBuilder@).
-}
module Interfaces (loadInterfaces) where

import           Control.Monad                 (foldM, liftM, unless)
import           Control.Monad.IO.Class        (liftIO)
import qualified Control.Monad.State    as S   (StateT (..), modify)
import           Data.List                     (intercalate, isPrefixOf)
import qualified Data.Map               as Map
import           Text.PrettyPrint

import           Curry.Base.Ident
import           Curry.Base.Message            (runMsg)
import           Curry.Base.Position
import qualified Curry.ExtendedFlat.Type as EF
import           Curry.Files.PathUtils   as PU
import           Curry.Syntax

import Base.Messages (Message, posMessage, internalError)

import Env.Interface

type IntfLoader a = S.StateT [Message] IO a

report :: Message -> IntfLoader ()
report msg = S.modify (msg:)

-- |Load the interface files into the 'InterfaceEnv'
loadInterfaces :: [FilePath] -> Module -> IO (InterfaceEnv, [Message])
loadInterfaces paths (Module m _ is _) = do
  (env, errs) <- S.runStateT action []
  return (env, reverse errs)
  where action = foldM (loadInterface paths [m]) initInterfaceEnv
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
              -> (Position, ModuleIdent) -> IntfLoader InterfaceEnv
loadInterface paths ctxt mEnv (p, m)
  | m `elem` ctxt       = do
    report $ errCyclicImport p $ m : takeWhile (/= m) ctxt
    return mEnv
  | m `Map.member` mEnv = return mEnv
  | otherwise           = do
      mbIntf <- liftIO $ PU.lookupCurryInterface paths m
      case mbIntf of
        Nothing   -> report (errInterfaceNotFound p m) >> return mEnv
        Just intf -> compileInterface paths ctxt mEnv m intf

-- |Compile an interface by recursively loading its dependencies
--
-- After reading an interface, all imported interfaces are recursively
-- loaded and entered into the interface's environment. There is no need
-- to check FlatCurry-Interfaces, since these files contain automatically
-- generated FlatCurry terms (type \texttt{Prog}).
compileInterface :: [FilePath] -> [ModuleIdent] -> InterfaceEnv
                 -> ModuleIdent -> FilePath -> IntfLoader InterfaceEnv
compileInterface paths ctxt mEnv m fn = do
  -- read module
  src <- liftIO $ readFile fn
  -- parse interface
  case runMsg $ parseInterface fn src of
    Left err -> report err >> return mEnv
    Right (intf@(Interface m' is _), _) -> do
      unless (m' == m) $ report $ errWrongInterface (first fn) m m'
      let importDecls = [ (pos, imp) | IImportDecl pos imp <- is ]
      mEnv' <- foldM (loadInterface paths (m : ctxt)) mEnv importDecls
      return $ Map.insert m intf mEnv'

{-
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
    = ITypeDecl pos (genQualIdent qn)
        (map genVarIndexIdent is)
        (RecordType (map genLabeledType cs) Nothing)
    | otherwise
    = IDataDecl pos (genQualIdent qn)
        (map genVarIndexIdent is)
        (map (Just . genConstrDecl) cs)
  genITypeDecl (EF.TypeSyn qn _ is t)
    = ITypeDecl pos (genQualIdent qn)
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
-}

errInterfaceNotFound :: Position -> ModuleIdent -> Message
errInterfaceNotFound p m = posMessage p $
  text "Interface for module" <+> text (moduleName m) <+> text "not found"

errWrongInterface :: Position -> ModuleIdent -> ModuleIdent -> Message
errWrongInterface p m m' = posMessage p $
  text "Expected interface for" <+> text (moduleName m)
  <> comma <+> text "but found" <+> text (moduleName m')

errCyclicImport :: Position -> [ModuleIdent] -> Message
errCyclicImport _ []  = internalError "Interfaces.errCyclicImport: empty list"
errCyclicImport p [m] = posMessage p $
  text "Recursive import for module" <+> text (moduleName m)
errCyclicImport p ms  = posMessage p $
  text "Cylic import dependency between modules"
  <+> text (intercalate ", " inits ++ " and " ++ lastm)
  where
  (inits, lastm)         = splitLast $ map moduleName ms
  splitLast []           = internalError "Interfaces.splitLast: empty list"
  splitLast (x : [])     = ([]  , x)
  splitLast (x : y : ys) = (x : xs, z) where (xs, z) = splitLast (y : ys)
