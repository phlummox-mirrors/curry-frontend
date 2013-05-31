
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
import System.FilePath
import System.Directory
import qualified Data.Set as Set
import Env.ClassEnv
import qualified Checks.TypeCheck as TC (typeCheck)
import Curry.Syntax (Module (..))
import Data.Maybe
import Debug.Trace

import Base.Types


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
    runM str _opts = checkDir str

-- | Check all curry/type files in the given directory
checkDir :: Dir -> IO Result
checkDir dir = do
  files <- getDirectoryContents (fn dir)
  let files'  = filter (\str -> ".curry" `isSuffixOf` str && str /= ".curry") files
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
  -- Always return success, also if there are error messages. 
  -- Note that here "False" is passed to TC.typeCheck so that no context
  -- reduction is done and we get the raw inferred contexts that we want!
  = CheckSuccess (env { tyConsEnv = tcEnv', valueEnv = tyEnv' }, mdl)
  where (tcEnv', tyEnv', _decls, _msgs) = TC.typeCheck (moduleIdent env)
          (tyConsEnv env) (valueEnv env) (classEnv env) False ds
  
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
    runM _str _opts = checkVarious
    
checkVarious :: IO Result
checkVarious = do
  let opts = CO.defaultOptions
  mod <- loadModule opts "test/typeclasses/TestVarious.curry" 
  let result = checkModule' opts mod
  case result of
    CheckSuccess tcEnv -> 
      if not $ checkScs tcEnv then return (Fail "check superclasses")
      else if not $ checkImpl (classEnv tcEnv) then return (Fail "implies")
      else if not $ checkValidCx (classEnv tcEnv) then return (Fail "isValidCx")
      else if not $ checkContextReduction (classEnv tcEnv) then return (Fail "context reduction")
      else if not $ checkFindPath (classEnv tcEnv) then return (Fail "find path") 
      else if not $ checkToHnf (classEnv tcEnv) then return (Fail "toHnf")
      else if not $ checkDictCode (classEnv tcEnv) then return (Fail "createDict")
      else if not $ checkDictType (classEnv tcEnv) then return (Fail "dictType")
      else return Pass
    CheckFailed msgs -> do print msgs; return (Fail "compilation error")

-- |Check that the superclasses are calculated correctly    
checkScs :: CompilerEnv -> Bool
checkScs env = 
  let cEnv = classEnv env in
  allSuperClasses cEnv (mkId "A") =:= [] &&
  allSuperClasses cEnv (mkId "B") =:= [] &&
  allSuperClasses cEnv (mkId "C") =:= map mkId ["A"] && 
  allSuperClasses cEnv (mkId "D") =:= map mkId ["A", "B", "E"] && 
  allSuperClasses cEnv (mkId "E") =:= [] &&
  allSuperClasses cEnv (mkId "F") =:= map mkId ["C", "D", "A", "B", "E"] &&
  allSuperClasses cEnv (mkId "G") =:= map mkId ["D", "A", "B", "E"] &&
  allSuperClasses cEnv (mkId "H") =:= map mkId ["F", "G", "C", "D", "A", "B", "E"] &&
  allSuperClasses cEnv (mkId "I") =:= [] &&
  allSuperClasses cEnv (mkId "J") =:= map mkId ["I"] &&
  allSuperClasses cEnv (mkId "K") =:= map mkId ["I", "J"] &&
  allSuperClasses cEnv (mkId "L") =:= map mkId ["K", "I", "J", "M"] &&
  allSuperClasses cEnv (mkId "M") =:= [] 


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


  implies cEnv [mk "A" 0] (mkId "A", list (mkTy 0)) &&
  not (implies cEnv [mk "A" 0] (mkId "A", tycon "T" [mkTy 0])) &&
  implies cEnv [mk "A" 0] (mkId "A", tycon "S" [mkTy 0]) &&
  implies cEnv [mk "B" 0] (mkId "A", tycon "U" [mkTy 0]) &&
  implies cEnv [mk "A" 0, mk "B" 1] (mkId "E", tycon "V" [mkTy 0, mkTy 1]) && 
  not (implies cEnv [mk "A" 0, mk "B" 0] (mkId "E", tycon "V" [mkTy 0, mkTy 1])) &&
  implies cEnv [mk "F" 0, mk "B" 1] (mkId "E", tycon "V" [mkTy 0, mkTy 1]) &&
  implies cEnv [mk "F" 0, mk "D" 1] (mkId "E", tycon "V" [mkTy 0, mkTy 1]) &&  
  
  implies cEnv [mk "A" 0] (mkId "A", list $ tycon "S" [mkTy 0]) &&
  implies' cEnv [mk "A" 0, mk "A" 1] 
    [(mkId "A", list $ tycon "S" [mkTy 0]), (mkId "A", list $ tycon "S" [mkTy 1])] &&
  implies cEnv [mk "A" 0] (mkId "A", list $ list $ tycon "S" [mkTy 0]) &&
  implies cEnv [mk "H" 0] (mkId "A", list $ tycon "S" [mkTy 0]) &&
  
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
  implies cEnv [mk "N" 0] (mkId "O", tycon "T" [mkTy 0]) &&
  
  implies cEnv [mk "N" 0] (mkId "N", TypeConstructor (qTupleIdP 2) [mkTy 0, mkTy 1]) &&
  implies cEnv [] (mkId "N", TypeConstructor qUnitIdP []) &&
  
  implies cEnv [] (mkId "N", tycon "Q" [mkTy 0]) &&
  
  not (implies cEnv [mk "A" 0] (mkId "C", tycon "X" [mkTy 0]))
  

mk :: String -> Int -> (QualIdent, Type)
mk str n = (mkId str, mkTy n)  

mkTy :: Int -> Type
mkTy n = TypeVariable n

tycon :: String -> [Type] -> Type
tycon s = TypeConstructor (mkQId' "TestVarious" s)

tyconP :: String -> [Type] -> Type
tyconP s = TypeConstructor (mkQId' "Prelude" s)

-- mkQId :: String -> QualIdent
-- mkQId s = mkQId' "TestVarious" s

mkQId' :: String -> String -> QualIdent
mkQId' m s = qualifyWith (mkMIdent [m]) $ mkIdent s

-- |checks the "isValidCx" function
checkValidCx :: ClassEnv -> Bool
checkValidCx cEnv = 
  null (isValidCx cEnv []) && 
  null (isValidCx cEnv [mk "N" 0]) && 
  null (isValidCx cEnv [(mkId "N", tycon "Q" [mkTy 0])]) &&
  not (null (isValidCx cEnv [(mkId "N", tycon "NotExistent" [mkTy 0])])) &&
  not (null $ isValidCx cEnv 
    [(mkId "A", tycon "U" [tycon "NotExistent" []])]) && 
  null (isValidCx cEnv 
    [(mkId "N", tycon "W" [tycon "R1" []])]) &&
  not (null $ isValidCx cEnv 
    [(mkId "N", tycon "W" [tycon "R2" []])])

(===) :: (Eq a, Show a) => a -> a -> Bool
x === y = if x == y then True else trace (show x ++ "/" ++ show y) False   

-- | checks the context reduction
checkContextReduction :: ClassEnv -> Bool
checkContextReduction cEnv =
  reduceContext cEnv [] == [] && 
  reduceContext cEnv [mk "H" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "H" 0, mk "F" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "H" 0, mk "G" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "H" 0, mk "F" 0, mk "G" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "F" 0, mk "H" 0, mk "G" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "F" 0, mk "G" 0, mk "H" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "F" 0, mk "G" 0, mk "H" 0, mk "D" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "F" 0, mk "G" 0, mk "H" 0, mk "D" 1] == [mk "H" 0, mk "D" 1] &&
  
  reduceContext cEnv [mk "H" 0, mk "H" 0] == [mk "H" 0] &&
  reduceContext cEnv [mk "H" 0, mk "H" 0, mk "H" 0] == [mk "H" 0] &&
  
  
  reduceContext cEnv [mk "A" 0, (mkId "A", list $ mkTy 0)] == [mk "A" 0] &&
  reduceContext cEnv [mk "A" 0, (mkId "A", list $ mkTy 1)] == [mk "A" 0, mk "A" 1] &&
  reduceContext cEnv 
    [mk "A" 0, (mkId "A", list $ mkTy 0), (mkId "A", list $ list $ mkTy 0)] == [mk "A" 0] &&
  reduceContext cEnv 
    [mk "G" 0, (mkId "A", list $ mkTy 0), (mkId "A", list $ list $ mkTy 0)] == [mk "G" 0] &&
  reduceContext cEnv 
    [(mkId "A", list $ mkTy 0), (mkId "A", list $ list $ mkTy 0)] == [(mk "A" 0)] &&
  
  reduceContext cEnv [mk "H" 0, mk "F" 0, mk "G" 0, (mkId "A", list $ mkTy 0), (mkId "A", list $ list $ mkTy 0)] == [mk "H" 0] &&
  
  reduceContext cEnv [(mkId "N", tycon "R1" [])] == [] && 
  reduceContext cEnv [mk "H" 0, (mkId "N", tycon "R1" [])] == [mk "H" 0] &&
  reduceContext cEnv [(mkId "N", tycon "NotExistent" [])] == [(mkId "N", tycon "NotExistent" [])] &&
    
  reduceContext cEnv [(mkId "Eq", tycon "T" [tyconP "Int" []])] == [] && 
  reduceContext cEnv [(mkId "Eq", tycon "T" [mkTy 0])] == [(mkId "Eq'", mkTy 0)] &&
  
  reduceContext cEnv [(mkId "Eq", tyconP "Float" [])] == [(mkId "Eq", tyconP "Float" [])] && 
  reduceContext cEnv [(mkId "Eq'", tyconP "Float" []), (mkId "Eq", tycon "T" [tyconP "Float" []])] ==
    [(mkId "Eq'", tyconP "Float" [])] && 
  reduceContext cEnv 
    [(mkId "Eq", tyconP "Int" []), (mkId "Eq", tyconP "Char" []), 
      (mkId "Eq", tyconP "(,)" [tyconP "Char" [], tyconP "Int" []])] =:=
    [(mkId "Eq", tyconP "Char" []), (mkId "Eq", tyconP "Int" [])]

-- | checks the findPath method
checkFindPath :: ClassEnv -> Bool
checkFindPath cEnv = 
  (findPath cEnv (mkId "H") (mkId "D") == Just [mkId "H", mkId "F", mkId "D"]
  || findPath cEnv (mkId "H") (mkId "D") == Just [mkId "H", mkId "G", mkId "D"]) &&
  findPath cEnv (mkId "H") (mkId "I") == Nothing &&
  findPath cEnv (mkId "L") (mkId "I") == Just [mkId "L", mkId "K", mkId "J", mkId "I"] &&
  -- takes shortest path?
  findPath cEnv (mkId "Q") (mkId "P") == Just [mkId "Q", mkId "P"] &&
  findPath cEnv (mkId "P") (mkId "Q") == Nothing &&
  findPath cEnv (mkId "K") (mkId "M") == Nothing &&
  findPath cEnv (mkId "F") (mkId "G") == Nothing &&
  findPath cEnv (mkId "G") (mkId "C") == Nothing &&
  findPath cEnv (mkId "C") (mkId "G") == Nothing &&
  isJust (findPath cEnv (mkId "H") (mkId "A")) &&
  isJust (findPath cEnv (mkId "H") (mkId "E")) &&
  isJust (findPath cEnv (mkId "H") (mkId "B")) &&
  isJust (findPath cEnv (mkId "F") (mkId "A")) &&
  isJust (findPath cEnv (mkId "F") (mkId "E")) &&
  isJust (findPath cEnv (mkId "F") (mkId "B"))

-- |checks toHnfs function
checkToHnf :: ClassEnv -> Bool
checkToHnf cEnv = 
  toHnf cEnv (mkId "Eq", tyconP "(,)" [mkTy 0, mkTy 1]) 
    == [mk "Eq" 0, mk "Eq" 1] &&
  toHnf cEnv (mkId "Eq", tyconP "(,)" [tyconP "Int" [], mkTy 1]) 
    == [(mkId "Eq", tyconP "Int" []), mk "Eq" 1] &&
  toHnf cEnv (mkId "Eq", tyconP "(,)" [mkTy 0, tyconP "Char" []]) 
    == [mk "Eq" 0, (mkId "Eq", tyconP "Char" [])] &&
  toHnf cEnv (mkId "Eq", tyconP "(,)" [tyconP "Int" [], tyconP "Char" []]) 
    == [(mkId "Eq", tyconP "Int" []), (mkId "Eq", tyconP "Char" [])] &&
    
  toHnf cEnv (mk "Eq" 0) == [mk "Eq" 0] &&
  
  toHnf cEnv (mkId "Eq", tycon "T" [mkTy 0]) == [(mkId "Eq'", mkTy 0)] &&
  
  toHnf cEnv (mkId "Eq", list $ list $ mkTy 0) == [(mkId "Eq", mkTy 0)] &&
  toHnf cEnv (mkId "Eq", tyconP "(,)" [list $ mkTy 0, mkTy 1])
    == [mk "Eq" 0, mk "Eq" 1]


-- |checks dictCode function
checkDictCode :: ClassEnv -> Bool
checkDictCode cEnv = 
  dictCode cEnv [mk "A" 0] (mk "A" 0) == Dictionary (mk "A" 0) &&
  dictCode cEnv [mk "A" 0, mk "A" 1] (mk "A" 0) == Dictionary (mk "A" 0) &&
  dictCode cEnv [mk "A" 0, mk "A" 1] (mk "A" 1) == Dictionary (mk "A" 1) &&
  
  dictCode cEnv [mk "K" 0] (mk "I" 0) == SelSuperClass (mk "K" 0) (mk "I" 0) &&
  dictCode cEnv [mk "K" 0] (mk "J" 0) == SelSuperClass (mk "K" 0) (mk "J" 0) && 
  dictCode cEnv [mk "L" 0] (mk "M" 0) == SelSuperClass (mk "L" 0) (mk "M" 0) &&
  
  dictCode cEnv [mk "A" 0] (mkId "A", list $ mkTy 0) 
    === BuildDict (mkId "A", list $ mkTy 0) [Dictionary $ mk "A" 0] &&
  dictCode cEnv [mk "A" 0, mk "A" 1] (mkId "A", list $ mkTy 0) 
    === BuildDict (mkId "A", list $ mkTy 0) [Dictionary $ mk "A" 0] &&
  dictCode cEnv [mk "A" 0, mk "A" 1] (mkId "A", list $ mkTy 1) 
    === BuildDict (mkId "A", list $ mkTy 1) [Dictionary $ mk "A" 1] &&
    
  dictCode cEnv [mk "F" 0] (mkId "A", list $ mkTy 0) 
    === BuildDict (mkId "A", list $ mkTy 0) [SelSuperClass (mk "F" 0) (mk "A" 0)] &&
    
  dictCode cEnv [] (mkId "Eq", tyconP "Bool" []) === BuildDict (mkId "Eq", tyconP "Bool" []) [] &&
  
  -- internalError
  -- dictCode cEnv [] (mkId "Eq", tyconP "Boolx" []) === Dictionary (mkId "Eq", tyconP "Boolx" [])
  
  dictCode cEnv [mk "Eq" 0, mk "Eq" 1] (mkId "Eq", pair (list $ mkTy 0) (mkTy 1))
    === BuildDict (mkId "Eq", pair (list $ mkTy 0) (mkTy 1))
                  [ BuildDict (mkId "Eq", list $ mkTy 0) [Dictionary (mk "Eq" 0)]
                  , Dictionary (mk "Eq" 1)
                  ] &&

  dictCode cEnv [mk "Ord" 0, mk "Ord" 1] (mkId "Eq", pair (list $ mkTy 0) (mkTy 1))
    === BuildDict (mkId "Eq", pair (list $ mkTy 0) (mkTy 1))
                  [ BuildDict (mkId "Eq", list $ mkTy 0) [SelSuperClass (mk "Ord" 0) (mk "Eq" 0)]
                  , SelSuperClass (mk "Ord" 1) (mk "Eq" 1)
                  ] 

list :: Type -> Type
list t = TypeConstructor qListIdP [t]

pair :: Type -> Type -> Type
pair t1 t2 = TypeConstructor (qTupleIdP 2) [t1, t2]


-- Checks the correctness of the dictType function
checkDictType :: ClassEnv -> Bool
checkDictType cEnv = 
  show (dictType cEnv (mkId "A1")) === 
    "(Prelude.(,,,,) (0 -> (1 -> Bool)) (0 -> 0) (0 -> (2 -> 3)) (0 -> 4) (0 -> (5 -> 5)))" &&
  show (dictType cEnv (mkId "B1")) === 
    "(Prelude.(,) (Prelude.(,,,,) (0 -> (1 -> Bool)) (0 -> 0) (0 -> (2 -> 3)) (0 -> 4) (0 -> (5 -> 5))) (0 -> (6 -> (7 -> (8 -> 0)))))" &&
  show (dictType cEnv (mkId "C1")) === "(0 -> 0)" &&
  show (dictType cEnv (mkId "E1")) === "(0 -> 0)" &&
  show (dictType cEnv (mkId "D1")) === 
    "(Prelude.(,,) (Prelude.(,) (Prelude.(,,,,) (0 -> (1 -> Bool)) (0 -> 0) (0 -> (2 -> 3)) (0 -> 4) (0 -> (5 -> 5))) (0 -> (6 -> (7 -> (8 -> 0))))) (0 -> 0) (0 -> (9 -> (10 -> 0))))" &&
  show (dictType cEnv (mkId "F1")) === "Prelude.()" &&
  show (dictType cEnv (mkId "G1")) === "Prelude.()" &&
  show (dictType cEnv (mkId "H1")) === "(Prelude.(,) Prelude.() (0 -> 0))" &&
  
  show (dictTypes cEnv [mkId "I1", mkId "J1"]) === "[(0 -> 1),(0 -> 2)]"
  

