-- {-# LANGUAGE FlexibleInstances #-}
module Main ( main ) where

-- import Distribution.TestSuite
import Prelude hiding (mod)
import Modules
import Checks
import Data.Char
import Data.List
import CompilerEnv
import qualified Curry.Syntax as CS
import qualified CompilerOpts as CO
import Text.PrettyPrint
import Curry.Syntax.Pretty hiding (ppContext)
import Env.Value
import Curry.Base.Ident
import System.Exit
import System.FilePath
import System.Directory

import Base.Types

main :: IO ()
main = do
  dirsContent <- readFile "test/typeCheckTests.txt"
  let dirs = filter (/= []) $ lines dirsContent
  mapM_ checkDir dirs 
  
  
checkDir :: FilePath -> IO ()
checkDir dir = do
  files <- getDirectoryContents dir
  let files'  = filter (\str -> ".curry" `isSuffixOf` str) files
      files'' = map dropExtension files'
  mapM_ checkTypes files''

location :: FilePath
location = "test/typeclasses/automated/"

checkTypes :: FilePath -> IO () -- Result
checkTypes file = do
  let opts = CO.defaultOptions
  mod <- loadModule opts (location ++ file ++ ".curry") 
  let (CheckSuccess tcEnv) = checkModule' opts mod
  types <- readFile (location ++ file ++ ".types")
  -- print (extractTypes types)
  let errs = doCheck tcEnv (extractTypes types)
  case errs of
    [] -> return () 
    _ -> do
      putStrLn ("Test for " ++ file ++ " failed for following functions: ")
      mapM_ putStrLn (map (\(x, y, z) -> x ++ " " ++ y ++ " " ++ z) errs)
      exitFailure
    
  
  
  
checkModule' :: CO.Options -> (CompilerEnv, CS.Module)
             -> CheckResult CompilerEnv
checkModule' opts (env, mdl) = do
  (env1,  kc) <- kindCheck env mdl -- should be only syntax checking ?
  (env2,  sc) <- syntaxCheck opts env1 kc
  (env3,  pc) <- precCheck        env2 sc
  (env4, tcc) <- typeClassesCheck env3 pc
  (env5, _tc) <- typeCheck env4 tcc
  return env5
  
  
extractTypes :: String -> [(String, String)]
extractTypes fileContent = 
  let lines0 = filter ((/= []) . trim) $ lines fileContent
      pairs = map (break (== ':')) lines0
  in -- remove ':'
     map (\(id0, ty0) -> (id0, trim $ tail ty0)) pairs

trim :: String -> String
trim str = removeDuplicateWhitespace $ reverse (dropWhile isSpace $ reverse (dropWhile isSpace str))

removeDuplicateWhitespace :: String -> String
removeDuplicateWhitespace [] = []
removeDuplicateWhitespace (c1:c2:cs) 
  | isSpace c1 && isSpace c2 = removeDuplicateWhitespace (c1:cs)
  | otherwise = c1 : removeDuplicateWhitespace (c2:cs)
removeDuplicateWhitespace (c:cs) = c : removeDuplicateWhitespace cs 




doCheck :: CompilerEnv -> [(String, String)] -> [(String, String, String)]
doCheck cEnv types = 
  concatMap findAndCmp types
  where
  findAndCmp :: (String, String) -> [(String, String, String)]
  findAndCmp (id0, ty0) = let
    (Value _ _ infType) = head' $ lookupValue (mkIdent id0) (valueEnv cEnv)
    infType' = show (ppTypeScheme infType)
    in if ty0 == infType'
       then []
       else [(id0, ty0, infType')]
  head' (x:_) = x
  head' [] = error "id not found"



ppTypeScheme :: TypeScheme -> Doc
ppTypeScheme (ForAll cx _n type0) = 
  ppContext cx <+> text "=>" <+> ppType type0


ppContext :: Context -> Doc
ppContext cx = parens $ hsep $ 
  punctuate comma (map (\(qid, ty) -> ppQIdent qid <+> ppType ty) cx')
  where cx' = sort $ nub cx

ppType :: Type -> Doc
ppType (TypeVariable n) = text (show n)
ppType (TypeConstructor c ts) = text (show c) <+> hsep (map ppType ts)
ppType (TypeArrow t1 t2) = parens $ ppType t1 <+> text "->" <+> ppType t2
ppType (TypeConstrained ts _n) 
  = text "constr" <> parens (hsep (map ppType ts))
ppType (TypeSkolem n) = text "skolem" <+> text (show n)
ppType (TypeRecord r n) 
  = text "record" <+> parens (text (show r) <+> text (show n))











