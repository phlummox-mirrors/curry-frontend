module Base.ErrorMessages where

import Data.List (intercalate)

import Curry.Base.Ident

errCyclicImport :: [ModuleIdent] -> String
errCyclicImport []  = error "Base.ErrorMessages.errCyclicImport: empty list"
errCyclicImport [m] = "Recursive import for module " ++ moduleName m
errCyclicImport ms  = "Cylic import dependency between modules "
                      ++ intercalate ", " inits ++ " and " ++ lastm
  where
  (inits, lastm)         = splitLast $ map moduleName ms
  splitLast []           = error "Base.ErrorMessages.splitLast: empty list"
  splitLast (x : [])     = ([]  , x)
  splitLast (x : y : ys) = (x : xs, z) where (xs, z) = splitLast (y : ys)

errMissingFile :: FilePath -> String
errMissingFile f = "Missing file \"" ++ f ++ "\""

errFileModuleMismatch :: FilePath -> ModuleIdent -> String
errFileModuleMismatch f m =  "File name '" ++ f
  ++ "' does not match module name '" ++ moduleName m ++ "'"

errModuleFileMismatch :: ModuleIdent -> String
errModuleFileMismatch mid = "module \"" ++ moduleName mid
  ++ "\" must be in a file \"" ++ moduleName mid ++ ".(l)curry\""

errWrongInterface :: ModuleIdent -> ModuleIdent -> String
errWrongInterface m m' =
  "Expected interface for " ++ show m ++ " but found " ++ show m'
  ++ show (moduleQualifiers m, moduleQualifiers m')

errWrongModule :: ModuleIdent -> ModuleIdent -> String
errWrongModule m m' =
  "Expected module for " ++ show m ++ " but found " ++ show m'
  ++ show (moduleQualifiers m, moduleQualifiers m')

errInterfaceNotFound :: ModuleIdent -> String
errInterfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

errInterfaceModuleMismatch :: ModuleIdent -> ModuleIdent -> String
errInterfaceModuleMismatch mi mm =
  "Interface " ++ show mi ++ " does not match module " ++ show mm
