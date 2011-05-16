{- |CurryCompilerOpts - Defines data structures containing options for
    compiling Curry programs (see module "CurryCompiler")

    September 2005, Martin Engelke (men@informatik.uni-kiel.de)
    March 2007    , extensions by Sebastian Fischer (sebf@informatik.uni-kiel.de)
    May 2011      , refinements by Björn Peemöller (bjp@informatik.uni-kiel.de)
-}
module CurryCompilerOpts
(Options (..), Dump (..), defaultOptions, compilerOpts, usage) where

import Data.List (nub)
import Data.Maybe (isJust)
import System.Console.GetOpt
import System.Environment (getArgs, getProgName)

import Curry.Files.Filenames (currySubdir)

-- |Data type for recording compiler options
data Options = Options
  { help               :: Bool           -- ^ show help
  , version            :: Bool           -- ^ show the version
  , force              :: Bool           -- ^ force compilation
  , html               :: Bool           -- ^ generate Html code
  , importPaths        :: [FilePath]     -- ^ directories for imports
  , output             :: Maybe FilePath -- ^ name of output file
  , noInterface        :: Bool   -- ^ do not create an interface file
  , noVerb             :: Bool   -- ^ verbosity on/off
  , noWarn             :: Bool   -- ^ warnings on/off
  , noOverlapWarn      :: Bool   -- ^ "overlap" warnings on/off
  , flat               :: Bool   -- ^ generate FlatCurry code
  , extendedFlat       :: Bool   -- ^ generate FlatCurry code with extensions
  , flatXml            :: Bool   -- ^ generate flat XML code
  , abstract           :: Bool   -- ^ generate typed AbstracCurry code
  , untypedAbstract    :: Bool   -- ^ generate untyped AbstractCurry code
  , parseOnly          :: Bool   -- ^ generate source representation
  , withExtensions     :: Bool   -- ^ enable extended functionalities
  , dump               :: [Dump] -- ^ dumps
  , writeToSubdir      :: Bool   -- ^ should the output be written to the subdir?
  , xNoImplicitPrelude :: Bool   -- ^ extension: no implicit import Prelude
  } deriving Show

-- TODO: dump FlatCurry code, dump AbstractCurry code, dump after 'case'
-- expansion

-- |Data type for representing code dumps
data Dump
  = DumpRenamed      -- ^ dump source after renaming
  | DumpTypes        -- ^ dump types after typechecking
  | DumpDesugared    -- ^ dump source after desugaring
  | DumpSimplified   -- ^ dump source after simplification
  | DumpLifted       -- ^ dump source after lambda-lifting
  | DumpIL           -- ^ dump IL code after translation
  | DumpCase         -- ^ dump IL code after case elimination
    deriving (Eq, Bounded, Enum, Show)

-- | Default compiler options
defaultOptions :: Options
defaultOptions = Options
  { help            = False
  , version         = False
  , force           = False
  , html            = False
  , importPaths     = []
  , output          = Nothing
  , noInterface     = False
  , noVerb          = False
  , noWarn          = False
  , noOverlapWarn   = False
  , flat            = False
  , extendedFlat    = False
  , flatXml         = False
  , abstract        = False
  , untypedAbstract = False
  , parseOnly       = False
  , withExtensions  = False
  , dump            = []
  , writeToSubdir   = True
  , xNoImplicitPrelude = False
  }

-- | All available compiler options
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
      (NoArg (\opts -> opts { help = True }))
      "display this help and exit"
  , Option "V"  ["version"]
      (NoArg (\opts -> opts { version = True }))
      "show the version number"
  , Option "f"  ["force"]
      (NoArg (\opts -> opts { force = True }))
      "force compilation of dependent files"
  , Option ""   ["html"]
      (NoArg (\opts -> opts { html = True }))
      "generate html code"
  , Option "i"  ["import-dir"]
      (ReqArg (\arg opts -> opts { importPaths = nub $ arg : importPaths opts }) "DIR")
      "search for imports in DIR"
  , Option "o"  ["output"]
      (ReqArg (\arg opts -> opts { output = Just arg }) "FILE")
      "write code to FILE"
  , Option ""   ["no-intf"]
      (NoArg (\opts -> opts { noInterface = True }))
      "do not create an interface file"
  , Option ""   ["no-verb"]
      (NoArg (\opts -> opts { noVerb = True }))
      "do not print compiler messages"
  , Option ""   ["no-warn"]
      (NoArg (\opts -> opts { noWarn = True }))
      "do not print warnings"
  , Option ""   ["no-overlap-warn"]
      (NoArg (\opts -> opts { noOverlapWarn = True }))
      "do not print warnings for overlapping rules"
  , Option ""   ["flat"]
      (NoArg (\opts -> opts { flat = True }))
      "generate FlatCurry code"
  , Option ""   ["extended-flat"]
      (NoArg (\opts -> opts { extendedFlat = True }))
      "generate FlatCurry code with source references"
  , Option ""   ["xml"]
      (NoArg (\opts -> opts { flatXml = True }))
      "generate flat xml code"
  , Option ""   ["acy"]
      (NoArg (\opts -> opts { abstract = True }))
      "generate (type infered) AbstractCurry code"
  , Option ""   ["uacy"]
      (NoArg (\opts -> opts { untypedAbstract = True }))
      "generate untyped AbstractCurry code"
  , Option ""   ["parse-only"]
      (NoArg (\opts -> opts { parseOnly = True }))
      "generate source representation"
  , Option "e"  ["extended"]
      (NoArg (\opts -> opts { withExtensions = True }))
      "enable extended Curry functionalities"
  , Option ""   ["dump-all"]
      (NoArg (\opts -> opts { dump = [minBound .. maxBound] }))
      "dump everything"
  , Option ""   ["dump-renamed"]
      (NoArg (\opts -> opts { dump = nub $ DumpRenamed : dump opts }))
      "dump source code after renaming"
  , Option ""   ["dump-types"]
      (NoArg (\opts -> opts { dump = nub $ DumpTypes : dump opts }))
      "dump types after type-checking"
  , Option ""   ["dump-desugared"]
      (NoArg (\opts -> opts { dump = nub $ DumpDesugared : dump opts }))
      "dump source code after desugaring"
  , Option ""   ["dump-simplified"]
      (NoArg (\opts -> opts { dump = nub $ DumpSimplified : dump opts }))
      "dump source code after simplification"
  , Option ""   ["dump-lifted"]
      (NoArg (\opts -> opts { dump = nub $ DumpLifted : dump opts }))
      "dump source code after lambda-lifting"
  , Option ""   ["dump-il"]
      (NoArg (\opts -> opts { dump = nub $ DumpIL : dump opts }))
      "dump intermediate language before lifting"
  , Option ""   ["dump-case"]
      (NoArg (\opts -> opts { dump = nub $ DumpCase : dump opts }))
      "dump intermediate language after case simplification"
  , Option ""   ["no-hidden-subdir"]
      (NoArg (\opts -> opts { writeToSubdir = False }))
      ("disable writing to hidden '" ++ currySubdir ++ "' subdirectory")
  , Option ""   ["x-no-implicit-prelude"]
        (NoArg (\opts -> opts { xNoImplicitPrelude = True }))
        ("do not implicitly 'import Prelude'")
  ]

parseOpts :: [String] -> (Options, [String], [String])
parseOpts args = (foldl (flip ($)) defaultOptions opts, files, errs) where
  (opts, files, errs) = getOpt Permute options args

-- |Check options and files and return a list of error messages
checkOpts :: Options -> [String] -> [String]
checkOpts opts files
  | isJust (output opts) && length files > 1
    = ["cannot specify -o with multiple targets"]
  | otherwise
    = []
    
-- |Print the usage information of the command line tool.
usage :: String -> String
usage prog = usageInfo header options
  where header = "usage: " ++ prog ++ " [OPTION] ... MODULE ..."

compilerOpts :: IO (String, Options, [String], [String])
compilerOpts = do
  args <- getArgs
  prog <- getProgName
  let (opts, files, errs) = parseOpts args
  return (prog, opts, files, errs ++ checkOpts opts files)
