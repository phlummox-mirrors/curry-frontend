-- $Id: cymk.hs,v 1.5 2003/09/03 13:23:09 wlux Exp $
--
-- Copyright (c) 2002-2003, Wolfgang Lux
-- See LICENSE for the full license.
--
-- Modified by Martin Engelke (men@informatik.uni-kiel.de)

import CurryDeps
import GetOpt
import Maybe
import Monad
import IO
import PathUtils
import System

data Options =
  Options{
    importPaths :: [FilePath],
    libPaths :: [FilePath],
    output :: Maybe FilePath,
    debug :: Bool,
    linkAlways :: Bool,
    mkDepend :: Bool,
    mkClean :: Bool,
    flat :: Bool,
    xml :: Bool,
    abstract :: Bool,
    untypedAbstract :: Bool
  }

defaultOptions =
  Options{
    importPaths = [],
    libPaths = [],
    output = Nothing,
    debug = False,
    linkAlways = False,
    mkDepend = False,
    mkClean = False,
    flat = False,
    xml = False,
    abstract = False,
    untypedAbstract = False
  }

data Option =
    Help | ImportPath FilePath | LibPath FilePath | Output FilePath
  | Debug | LinkAlways | Clean | Depend | Flat | XML
  | Abstract | UntypedAbstract
  deriving Eq

options = [
    Option "a" ["link-always"] (NoArg LinkAlways)
           "always relink the target file",
    Option "g" ["debug"] (NoArg Debug)
           "compile with debugging information",
    Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
           "search for imported modules in DIR",
    Option "M" ["depend"] (NoArg Depend)
           "create Makefile dependencies for all targets",
    Option "o" ["output"] (ReqArg Output "FILE")
           "output goes to FILE",
    Option "P" ["lib-dir"] (ReqArg LibPath "DIR")
           "search for library interfaces in DIR",
    Option ""  ["clean"] (NoArg Clean)
           "remove compiled file for all targets",
    Option ""  ["flat"] (NoArg Flat)
           "generate FlatCurry code",
    Option ""  ["xml"] (NoArg XML)
           "generate flat xml code",
    Option ""  ["acy"] (NoArg Abstract)
           "generate (type infered) AbstractCurry code",
    Option ""  ["uacy"] (NoArg UntypedAbstract)
           "generate untyped AbstractCurry code",
    Option "?h" ["help"] (NoArg Help)
           "display this help and exit"
  ]

selectOption (ImportPath dir) opts =
  opts{ importPaths = dir : importPaths opts }
selectOption (LibPath dir) opts = opts{ libPaths = dir : libPaths opts }
selectOption (Output file) opts = opts{ output = Just file }
selectOption Debug opts = opts{ debug = True }
selectOption LinkAlways opts = opts{ linkAlways = True }
selectOption Depend opts = opts{ mkDepend = True }
selectOption Clean opts = opts{ mkClean = True }
selectOption Flat opts = opts{ flat = True }
selectOption XML opts = opts{ xml = True }
selectOption Abstract opts = opts{ abstract = True }
selectOption UntypedAbstract opts = opts{ untypedAbstract = True }

main :: IO ()
main =
  do
    prog <- getProgName
    args <- getArgs
    curryImports <- catch (getEnv "CURRY_IMPORTS" >>= return . pathList)
                          (const (return []))
    cymk prog args curryImports

cymk :: String -> [String] -> [FilePath] -> IO ()
cymk prog args curryImports
  | Help `elem` opts = printUsage prog
  | null errs = processFiles cymkOpts prog files
  | otherwise = badUsage prog errs
  where (opts,files,errs) = getOpt Permute options args
        cymkOpts =
	  foldr selectOption defaultOptions{ libPaths = curryImports } opts

printUsage :: String -> IO ()
printUsage prog =
  do
    putStrLn (usageInfo (unlines header) options)
    exitWith (ExitSuccess)
  where header = ["usage: " ++ prog ++ " [OPTION]... MODULE ..."]

badUsage :: String -> [String] -> IO ()
badUsage prog errs =
  do
    mapM_ (putErr . mkErrorLine) errs
    putErrLn ("Try `" ++ prog ++ " --help' for more information")
    exitWith (ExitFailure 1)
  where mkErrorLine err = prog ++ ": " ++ err

processFiles :: Options -> String -> [String] -> IO ()
processFiles opts prog files
  | null files = badUsage prog ["no modules\n"]
  | mkDepend opts && mkClean opts =
      badUsage prog ["cannot specify --clean with --depend\n"]
  | mkDepend opts =
      makeDepend (importPaths opts) (libPaths opts) (output opts) files
  | isJust (output opts) && length files > 1 =
      badUsage prog ["cannot specify -o with multiple targets\n"]
  | otherwise = 
      do
        es <- fmap concat (mapM script files)
	unless (null es) (mapM putErrLn es >> exitWith (ExitFailure 2))
  where 
     script = buildScript (mkClean opts) (debug opts) (linkAlways opts) 
	                  (flat opts) (xml opts)
			  (abstract opts) (untypedAbstract opts)
	                  (importPaths opts) (libPaths opts) (output opts)

putErr, putErrLn :: String -> IO ()
putErr = hPutStr stderr
putErrLn = hPutStr stderr . (++ "\n")

-------------------------------------------------------------------------------
