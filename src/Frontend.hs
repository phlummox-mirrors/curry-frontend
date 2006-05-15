-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- Frontend - Provides an API for dealing with several kinds of Curry
--            program representations
--
-- December 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module Frontend (lex, parse, fullParse, typingParse, abstractIO, flatIO,
		 Result(..), Message(..)
		)where

import Modules
import CurryBuilder
import CurryCompiler
import CurryCompilerOpts
import CurryParser
import CurryLexer
import GenAbstractCurry
import GenFlatCurry
import CaseCompletion
import CurryDeps hiding (unlitLiterate)
import qualified CurrySyntax as CS
import qualified AbstractCurry as ACY
import qualified FlatCurry as FCY
import qualified Error as Err
import CompilerResults
import Message
import CurryEnv
import Unlit
import Ident
import Position
import PathUtils
import Env
import List
import Maybe
import Monad
import System
import Prelude hiding (lex)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Returns the result of a lexical analysis of the source program 'src'.
-- The result is a list of tuples consisting of a position and a token
-- (see Modules "Position" and "CurryLexer")
lex :: FilePath -> String -> Result [(Position,Token)]
lex fn src = genToks (lexFile (first fn) src False [])


-- Returns the result of a syntactical analysis of the source program 'src'.
-- The result is the syntax tree of the program (type 'Module'; see Module
-- "CurrySyntax").
parse :: FilePath -> String -> Result CS.Module
parse fn src = let (err, src') = unlitLiterate fn src
	       in  if null err
		   then genCurrySyntax fn (parseSource True fn src')
		   else Failure [message_ Error err]


-- Returns the syntax tree of the source program 'src' (type 'Module'; see
-- Module "CurrySyntax") after resolving the category (i.e. function,
-- constructor or variable) of an identifier. 'fullParse' always
-- searches for standard Curry libraries in the path defined in the
-- environment variable "PAKCSLIBPATH". Additional search paths can
-- be defined using the argument 'paths'.
fullParse :: [FilePath] -> FilePath -> String -> IO (Result CS.Module)
fullParse paths fn src =
  do importPaths <- getCurryImports
     genFullCurrySyntax simpleCheckModule (paths ++ importPaths)
			fn (parse fn src)

-- Behaves like 'fullParse', but Returns the syntax tree of the source 
-- program 'src' (type 'Module'; see Module "CurrySyntax") after inferring 
-- the types of identifiers.
typingParse :: [FilePath] -> FilePath -> String -> IO (Result CS.Module)
typingParse paths fn src = 
  do importPaths <- getCurryImports
     genFullCurrySyntax checkModule (paths ++ importPaths)
			fn (parse fn src)

-- Compiles the source programm 'src' to an AbstractCurry program.
-- 'fullParse' always searches for standard Curry libraries in the path 
-- defined in the environment variable "PAKCSLIBPATH". Additional search 
-- paths can be defined using the argument 'paths'.
-- Notes: Due to the lack of error handling in the current version of the
-- front end, this function may fail when an error occurs
abstractIO :: [FilePath] -> FilePath -> String -> IO (Result ACY.CurryProg)
abstractIO paths fn src = 
  do importPaths <- getCurryImports
     genAbstractIO (paths ++ importPaths) fn (parse fn src)


-- Compiles the source program 'src' to a FlatCurry program.
-- 'fullParse' always searches for standard Curry libraries in the path 
-- defined in the environment variable "PAKCSLIBPATH". Additional search 
-- paths can be defined using the argument 'paths'.
-- Note: Due to the lack of error handling in the current version of the
-- front end, this function may fail when an error occurs
flatIO :: [FilePath] -> FilePath -> String -> IO (Result FCY.Prog)
flatIO paths fn src = 
  do importPaths <- getCurryImports
     genFlatIO (paths ++ importPaths) fn (parse fn src)


-------------------------------------------------------------------------------
-- Result handling

data Result a = Result [Message] a | Failure [Message] deriving Show

-- See module "Message":

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Privates...


opts paths = defaultOpts{ 
                     importPaths = paths,
		     noVerb      = True,
		     noWarn      = True,
		     abstract    = True
		   }


--
genToks :: Err.Error [(Position,Token)] -> Result [(Position,Token)]
genToks (Err.Ok toks)   = Result [] toks
genToks (Err.Error err) = Failure [message_ Error err]


--
genCurrySyntax :: FilePath -> Err.Error CS.Module -> Result (CS.Module)
genCurrySyntax fn (Err.Ok mod)
   = let mod'@(CS.Module mid _ _) = patchModuleId fn (importPrelude fn mod)
     in  if isValidModuleId fn mid
	 then Result [] mod'
	 else Failure [message_ Error (err_invalidModuleName mid)]
genCurrySyntax _ (Err.Error err)
   = Failure [message_ Error err]


--
genFullCurrySyntax check paths fn (Result msgs mod)
   = do errs <- makeInterfaces paths mod
	if null errs
	   then do mEnv <- loadInterfaces paths mod
		   (_, _, _, mod', _, msgs') <- check (opts paths) mEnv mod
		   return (Result (msgs ++ msgs') mod')
	   else return (Failure (msgs ++ map (message_ Error) errs))
genFullCurrySyntax _ _ _ (Failure msgs) = return (Failure msgs)


--
genAbstractIO :: [FilePath] -> FilePath -> Result CS.Module
	      -> IO (Result ACY.CurryProg)
genAbstractIO paths fn (Result msgs mod)
   = do errs <- makeInterfaces paths mod
	if null errs
	   then do mEnv <- loadInterfaces paths mod
		   (tyEnv, tcEnv, _, mod', _, msgs')
		       <- simpleCheckModule (opts paths) mEnv mod
		   return (Result (msgs ++ msgs') 
			          (genTypedAbstract tyEnv tcEnv mod'))
	   else return (Failure (msgs ++ map (message_ Error) errs))
genAbstractIO _ _ (Failure msgs) = return (Failure msgs)


--
genFlatIO :: [FilePath] -> FilePath -> Result CS.Module -> IO (Result FCY.Prog)
genFlatIO paths fn (Result msgs mod)
   = do errs <- makeInterfaces paths mod
	if null errs then
	   (do mEnv <- loadInterfaces paths mod
	       (tyEnv, tcEnv, aEnv, mod', intf, msgs') <- 
	           checkModule (opts paths) mEnv mod
	       let (il, aEnv', _) 
	              = transModule True False False mEnv tyEnv tcEnv aEnv mod'
	           il' = completeCase mEnv il
	           cEnv = curryEnv mEnv tcEnv intf mod'
	           (prog,msgs'') = genFlatCurry (opts paths) cEnv mEnv 
	                                        tyEnv tcEnv aEnv' il'
               return (Result (msgs'' ++ msgs ++ msgs') prog)
	   )
	   else return (Failure (msgs ++ map (message_ Error) errs))
genFlatIO _ _ (Failure msgs) = return (Failure msgs)


-------------------------------------------------------------------------------

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces ::  [FilePath] -> CS.Module -> IO [String]
makeInterfaces paths (CS.Module mid _ decls)
  = do let imports = [preludeMIdent | mid /= preludeMIdent] 
		      ++ [imp | CS.ImportDecl _ imp _ _ _ <- decls]
       (deps, errs) <- fmap (flattenDeps . sortDeps)
		            (foldM (moduleDeps paths []) emptyEnv imports)
       when (null errs) (mapM_ (compile deps . snd) deps)
       return errs
 where
 compile deps (Source file' mods)
    = do smake [flatName file', flatIntName file']
	       (file':catMaybes (map (flatInterface deps) mods))
	       (compileCurry (opts paths) file')
	       (return defaultResults)
	 return ()
 compile _ _ = return ()

 flatInterface deps mod 
    = case (lookup mod deps) of
        Just (Source file _)  -> Just (flatIntName (rootname file))
	Just (Interface file) -> Just (flatIntName (rootname file))
	_                     -> Nothing

-- Declares the filename as module name, if the module name is not
-- explicitly declared in the module.
patchModuleId :: FilePath -> CS.Module -> CS.Module
patchModuleId fn (CS.Module mid mexports decls)
   | (moduleName mid) == "main"
     = CS.Module (mkMIdent [basename (rootname fn)]) mexports decls
   | otherwise
     = CS.Module mid mexports decls


-- Adds an import declaration for the prelude to the module, if
-- it is not the prelude itself. If the module already has an explicit
-- import for the prelude, then a qualified import is added.
importPrelude :: FilePath -> CS.Module -> CS.Module
importPrelude fn (CS.Module m es ds)
   = CS.Module m es (if m == preludeMIdent then ds else ds')
 where ids = [decl | decl@(CS.ImportDecl _ _ _ _ _) <- ds]
       ds' = CS.ImportDecl (first fn) preludeMIdent
                        (preludeMIdent `elem` map importedModule ids)
                        Nothing Nothing : ds
       importedModule (CS.ImportDecl _ m q asM is) = fromMaybe m asM


-- Returns 'True', if file name and module name are equal.
isValidModuleId :: FilePath -> ModuleIdent -> Bool
isValidModuleId fn mid
   = last (moduleQualifiers mid) == basename (rootname fn)


-- Converts a literate source program to a non-literate source program
unlitLiterate :: FilePath -> String -> (String,String)
unlitLiterate fn src
  | isLiterateSource fn = unlit fn src
  | otherwise           = ("",src)

isLiterateSource :: FilePath -> Bool
isLiterateSource fn = litExt `isSuffixOf` fn

litExt = ".lcurry"


-------------------------------------------------------------------------------
-- Messages

err_invalidModuleName :: ModuleIdent -> String
err_invalidModuleName mid 
   = "module \"" ++ moduleName mid 
     ++ "\" must be in a file \"" ++ moduleName mid ++ ".curry\""


-------------------------------------------------------------------------------
-- Curry library paths

-- Environment variables containing paths to Curry libraries
importVars = ["PAKCSLIBPATH"]


-- Returns a list of the paths to the Curry libraries
getCurryImports :: IO [FilePath]
getCurryImports
   = do imps <- mapM sureGetEnv importVars
	return (concatMap pathList imps)


-- Returns the value of an environment variable, if it exists, otherwise an
-- empty string.
sureGetEnv :: String -> IO String
sureGetEnv env = catch (getEnv env) (const (return ""))


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------