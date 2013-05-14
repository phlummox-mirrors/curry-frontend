
module TestTypeChecking ( tests, checkDir, Dir (..) ) where

import Distribution.TestSuite
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
import Control.Monad
import qualified Data.Set as Set
import Env.ClassEnv
import qualified Checks.TypeCheck as TC (typeCheck)
import Curry.Syntax (Module (..))

import Base.Types hiding (ppContext)


tests :: [Test]
tests =
  [ -- TODO: read test directories from external file?
    impure (Dir "test/typeclasses/automated/")
  , impure (Various "test")]

-- ----------------------------------------------------------------------------
-- Check type checking by comparing the inferred types with the types 
-- given in a special file. In the given folder, the file "Name.curry" must
-- have a file "Name.types" with the given types. 
-- ----------------------------------------------------------------------------

data Dir = Dir { fn :: String }

instance TestOptions Dir where
    name = fn
    options = const []
    defaultOptions _ = return (Options [])
    check _ _ = []

instance ImpureTestable Dir where
    runM str opts = checkDir str

-- | Check all curry/type files in the given directory
checkDir :: Dir -> IO Result
checkDir dir = do
  files <- getDirectoryContents (fn dir)
  let files'  = filter (\str -> ".curry" `isSuffixOf` str) files
      files'' = map dropExtension files'
  success <- mapM checkTypes files''
  case (any not success) of
    True -> return (Fail "checkDir")
    False -> return Pass 
  

location :: FilePath
location = "test/typeclasses/automated/"

-- | Reads a curry and the corresponding type file and checks whether
-- the inferred types match the types given in the type file. 
-- The lines in the type file has the format
-- @
-- # comment
-- funName: type
-- @
-- The type given must not have less whitespace than the pretty printed type 
-- (see pretty printing functions below), but more whitespace is allowed. 
-- Furthermore the given type must have all brackets that are outputted by the
-- pretty printing functions (for simplicity)  
checkTypes :: FilePath -> IO Bool -- Result
checkTypes file = do
  putStrLn ("checking " ++ file)
  let opts = CO.defaultOptions
  mod <- loadModule opts (location ++ file ++ ".curry") 
  let result = checkModule' opts mod
  case result of
    CheckSuccess tcEnv -> do
      types <- readFile (location ++ file ++ ".types")
      -- print (extractTypes types)
      let errs = doCheck tcEnv (extractTypes types)
      case errs of
        [] -> return True
        _ -> do
          putStrLn ("\nTest for " ++ file ++ " failed for following functions: ")
          mapM_ putStrLn (map (\(x, y, z) -> x ++ "\n  " ++ y ++ "\n  " ++ z) errs)
          return False
    CheckFailed msgs -> do print msgs; return False  
    
{-  
loadAndCheck :: FilePath -> IO (CheckResult CompilerEnv)
loadAndCheck str =
-}   

-- |This function checks the modules until the type check phase is reached
checkModule' :: CO.Options -> (CompilerEnv, CS.Module)
             -> CheckResult CompilerEnv
checkModule' opts (env, mdl) = do
  (env1,  kc) <- kindCheck env mdl -- should be only syntax checking ?
  (env2,  sc) <- syntaxCheck opts env1 kc
  (env3,  pc) <- precCheck        env2 sc
  (env4, tcc) <- typeClassesCheck env3 pc
  (env5, _tc) <- typeCheck' env4 tcc
  return env5
  
  
typeCheck' :: CompilerEnv -> Module -> CheckResult (CompilerEnv, Module)
typeCheck' env mdl@(Module _ _ _ ds)
  -- always return success, also if there are error messages
  {-| null msgs-} = CheckSuccess (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, mdl)
  -- | otherwise = CheckFailed msgs
  where (tcEnv', tyEnv', msgs) = TC.typeCheck (moduleIdent env)
                                 (tyConsEnv env) (valueEnv env) (classEnv env) ds
  
-- |This function extracts the (function name, type) pairs from the types
-- file. 
extractTypes :: String -> [(String, String)]
extractTypes fileContent = 
  let lines0 = filter ((/= []) . trim) $ lines fileContent
      -- remove comment lines
      lines1 = filter (not . (== '#') . head) lines0
      pairs = map (break (== ':')) lines1
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



-- |compares a (function name, type) pair from the type file with the 
-- inferred type from the value environment. If they match, the empty list
-- is returned, else the triple with the function name, the expected type, 
-- and the inferred type
doCheck :: CompilerEnv -> [(String, String)] -> [(String, String, String)]
doCheck cEnv types = 
  concatMap findAndCmp types
  where
  findAndCmp :: (String, String) -> [(String, String, String)]
  findAndCmp (id0, ty0) = let
    (Value _ _ infType) = head' $ lookupValue (read id0) (valueEnv cEnv)
    infType' = show (ppTypeScheme infType)
    in if ty0 == infType'
       then []
       else [(id0, ty0, infType')]
    where
    head' (x:_) = x
    head' [] = error ("id " ++ id0 ++ " not found")

      
-- ----------------------------------------------------------------------------
-- Pretty printing functions for the types. Note that the types given in the
-- type file must exaclty (except for whitespace) match the output of these
-- functions
-- ----------------------------------------------------------------------------


ppTypeScheme :: TypeScheme -> Doc
ppTypeScheme (ForAll cx _n type0) = 
  ppContext cx <+> text "=>" <+> ppType type0


ppContext :: Context -> Doc
ppContext cx = parens $ hsep $ 
  punctuate comma (map (\(qid, ty) -> ppQIdent qid <+> ppType ty) cx')
  where cx' = sort $ nub cx

ppType :: Type -> Doc
ppType (TypeVariable n) = text (show n)
ppType (TypeConstructor c ts) = 
  (if length ts == 0 then id else parens) $ text (show c) <+> hsep (map ppType ts)
ppType (TypeArrow t1 t2) = parens $ ppTypeCon t1 True <+> text "->" <+> ppTypeCon t2 True
ppType (TypeConstrained ts _n) 
  = text "constr" <> parens (hsep (map ppType ts))
ppType (TypeSkolem n) = text "skolem" <+> text (show n)
ppType (TypeRecord r n) 
  = text "record" <+> parens (text (show r) <+> text (show n))


ppTypeCon :: Type -> Bool -> Doc
ppTypeCon (TypeConstructor c ts) _arrow = 
  {-(if length ts /= 0 && not arrow then parens else id) $-}
  text (show c) <+> hsep (map ppType ts)
ppTypeCon t _arrow = ppType t

-- ----------------------------------------------------------------------------
-- Check various class related functions:
--   * Correct superclass calculation
--   * Correctness of the implies function
-- ----------------------------------------------------------------------------

data Various = Various { vFn :: FilePath}

instance TestOptions Various where
    name = vFn
    options = const []
    defaultOptions _ = return (Options [])
    check _ _ = []

instance ImpureTestable Various where
    runM str opts = checkVarious
    
checkVarious :: IO Result
checkVarious = do
  let opts = CO.defaultOptions
  mod <- loadModule opts "test/typeclasses/TestVarious.curry" 
  let result = checkModule' opts mod
  case result of
    CheckSuccess tcEnv -> 
      if not $ checkScs tcEnv then return (Fail "check superclasses")
      else if not $ checkImpl (classEnv tcEnv) then return (Fail "implies")
      else return Pass
    CheckFailed msgs -> do print msgs; return (Fail "compilation error")

-- |Check that the superclasses are calculated correctly    
checkScs :: CompilerEnv -> Bool
checkScs env = 
  let cEnv = classEnv env in
  allSuperClasses' cEnv (mkId "A") =:= [] &&
  allSuperClasses' cEnv (mkId "B") =:= [] &&
  allSuperClasses' cEnv (mkId "C") =:= map mkId ["A"] && 
  allSuperClasses' cEnv (mkId "D") =:= map mkId ["A", "B", "E"] && 
  allSuperClasses' cEnv (mkId "E") =:= [] &&
  allSuperClasses' cEnv (mkId "F") =:= map mkId ["C", "D", "A", "B", "E"] &&
  allSuperClasses' cEnv (mkId "G") =:= map mkId ["D", "A", "B", "E"] &&
  allSuperClasses' cEnv (mkId "H") =:= map mkId ["F", "G", "C", "D", "A", "B", "E"] &&
  allSuperClasses' cEnv (mkId "I") =:= [] &&
  allSuperClasses' cEnv (mkId "J") =:= map mkId ["I"] &&
  allSuperClasses' cEnv (mkId "K") =:= map mkId ["I", "J"] &&
  allSuperClasses' cEnv (mkId "L") =:= map mkId ["K", "I", "J", "M"] &&
  allSuperClasses' cEnv (mkId "M") =:= [] 


(=:=) :: Ord a => [a] -> [a] -> Bool
xs =:= ys = (Set.fromList xs) == (Set.fromList ys)

mkId :: String -> QualIdent
mkId s = qualify $ mkIdent s

-- |check that the implies function works correctly
checkImpl :: ClassEnv -> Bool
checkImpl cEnv = 
  implies cEnv [mk "A" 0] (mk "A" 0) &&
  not (implies cEnv [mk "A" 0] (mk "B" 0)) &&
  implies cEnv [mk "D" 0] (mk "A" 0) &&
  implies cEnv [mk "H" 0] (mk "A" 0) &&
  implies cEnv [mk "D" 0, mk "F" 0] (mk "A" 0) &&
  implies cEnv [mk "D" 0, mk "E" 0] (mk "A" 0) &&
  not (implies cEnv [mk "A" 0, mk "B" 0] (mk "E" 0)) &&
  implies cEnv [mk "L" 0] (mk "I" 0) &&
  not (implies cEnv [mk "I" 0] (mk "L" 0)) &&
  implies' cEnv [mk "F" 0, mk "G" 0] [mk "C" 0, mk "D" 0] &&
  not (implies cEnv [mk "A" 0] (mk "I" 0)) &&
  
  
  not (implies cEnv [mk "A" 1] (mk "A" 0)) &&
  not (implies cEnv [mk "H" 0] (mk "A" 1)) &&
  not (implies cEnv [mk "F" 0, mk "G" 1] (mk "C" 1)) &&
  implies' cEnv [mk "F" 0, mk "G" 1] [mk "C" 0, mk "D" 0, mk "D" 1] &&


  implies cEnv [mk "A" 0] (mkId "A", TypeConstructor qListId [mkTy 0]) &&
  not (implies cEnv [mk "A" 0] (mkId "A", TypeConstructor (mkId "T") [mkTy 0])) &&
  implies cEnv [mk "A" 0] (mkId "A", TypeConstructor (mkId "S") [mkTy 0]) &&
  implies cEnv [mk "B" 0] (mkId "A", TypeConstructor (mkId "U") [mkTy 0]) &&
  implies cEnv [mk "A" 0, mk "B" 1] (mkId "E", TypeConstructor (mkId "V") [mkTy 0, mkTy 1]) && 
  not (implies cEnv [mk "A" 0, mk "B" 0] (mkId "E", TypeConstructor (mkId "V") [mkTy 0, mkTy 1])) &&
  implies cEnv [mk "F" 0, mk "B" 1] (mkId "E", TypeConstructor (mkId "V") [mkTy 0, mkTy 1]) &&
  implies cEnv [mk "F" 0, mk "D" 1] (mkId "E", TypeConstructor (mkId "V") [mkTy 0, mkTy 1]) &&  
  
  implies cEnv [mk "A" 0] (mkId "A", TypeConstructor qListId [TypeConstructor (mkId "S") [mkTy 0]]) &&
  implies cEnv [mk "A" 0] (mkId "A", TypeConstructor qListId [TypeConstructor qListId [TypeConstructor (mkId "S") [mkTy 0]]]) &&
  implies cEnv [mk "H" 0] (mkId "A", TypeConstructor qListId [TypeConstructor (mkId "S") [mkTy 0]]) &&
  
  implies cEnv [mk "E" 0] (mkId "E", TypeArrow (mkTy 0) (mkTy 1)) &&
  not (implies cEnv [mk "E" 1] (mkId "E", TypeArrow (mkTy 0) (mkTy 1))) &&
  not (implies cEnv [mk "A" 0, mk "C" 1] (mkId "E", TypeArrow (mkTy 0) (mkTy 1))) &&
  implies cEnv [mk "H" 0] (mkId "E", TypeArrow (mkTy 0) (mkTy 1)) &&
  not (implies cEnv [mk "H" 1] (mkId "E", TypeArrow (mkTy 0) (mkTy 1))) &&
  
  not (implies cEnv [] (mkId "I", TypeArrow (mkTy 0) (mkTy 1))) &&
  not (implies cEnv [mk "M" 0] (mkId "I", TypeArrow (mkTy 0) (mkTy 1))) &&
  not (implies cEnv [mk "K" 0] (mkId "I", TypeArrow (mkTy 0) (mkTy 1))) &&
  implies cEnv [mk "M" 0, mk "K" 0] (mkId "I", TypeArrow (mkTy 0) (mkTy 1)) &&
  
  not (implies cEnv [] (mk "E" 0)) &&
  not (implies' cEnv [] [mk "E" 0, mk "F" 0]) &&
  implies' cEnv [] [] &&
  implies' cEnv [mk "E" 0] [] &&
  
  not (implies cEnv [mk "N" 0] (mk "O" 0)) &&
  implies cEnv [mk "N" 0] (mk "N" 0) &&
  not (implies cEnv [mk "O" 0] (mk "N" 0)) &&
  implies cEnv [mk "N" 0] (mkId "O", TypeConstructor (mkId "T") [mkTy 0]) &&
  
  implies cEnv [mk "N" 0] (mkId "N", TypeConstructor (qTupleId 2) [mkTy 0, mkTy 1]) &&
  implies cEnv [] (mkId "N", TypeConstructor qUnitId []) &&
  
  implies cEnv [] (mkId "N", TypeConstructor (mkId "Q") [mkTy 0])
  

mk :: String -> Int -> (QualIdent, Type)
mk str n = (mkId str, mkTy n)  

mkTy :: Int -> Type
mkTy n = TypeVariable n
