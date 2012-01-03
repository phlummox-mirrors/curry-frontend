{- |
    Module      :  $Header$
    Description :  Compiler options
    Copyright   :  (c) 2005, Martin Engelke (men@informatik.uni-kiel.de)
                       2007, Sebastian Fischer (sebf@informatik.uni-kiel.de)
                       2011, Björn Peemöller (bjp@informatik.uni-kiel.de)
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines data structures containing options for the
    compilation of Curry programs.
-}
module CompilerOpts
  ( Options (..), CymakeMode (..), Verbosity (..), TargetType (..)
  , Extension (..), DumpLevel (..), defaultOptions, compilerOpts, usage
  ) where

import Data.List (intercalate, nub)
import Data.Maybe (isJust)
import System.Console.GetOpt
import System.Environment (getArgs, getProgName)
import System.FilePath (splitSearchPath)

import Curry.Files.Filenames (currySubdir)

-- |Data type for recording compiler options
data Options = Options
  -- general
  { optMode         :: CymakeMode     -- ^ show help
  , optVerbosity    :: Verbosity      -- ^ verbosity level
  -- compilation
  , optForce        :: Bool           -- ^ force compilation of target
  , optLibraryPaths :: [FilePath]     -- ^ directories for libraries
  , optImportPaths  :: [FilePath]     -- ^ directories for imports
  , optOutput       :: Maybe FilePath -- ^ name of output file
  , optUseSubdir    :: Bool           -- ^ use subdir for output?
  , optInterface    :: Bool           -- ^ create an interface file
  , optWarn         :: Bool           -- ^ show warnings
  , optOverlapWarn  :: Bool           -- ^ show "overlap" warnings
  , optTargetTypes  :: [TargetType]   -- ^ what to generate
  , optExtensions   :: [Extension]    -- ^ enabled language extensions
  , optDumps        :: [DumpLevel]    -- ^ dump levels
  }

-- | Default compiler options
defaultOptions :: Options
defaultOptions = Options
  { optMode         = ModeMake
  , optVerbosity    = VerbStatus
  , optForce        = False
  , optLibraryPaths = []
  , optImportPaths  = []
  , optOutput       = Nothing
  , optUseSubdir    = True
  , optInterface    = True
  , optWarn         = True
  , optOverlapWarn  = True
  , optTargetTypes  = []
  , optExtensions   = []
  , optDumps        = []
  }

data CymakeMode
  = ModeHelp
  | ModeVersion
  | ModeNumericVersion
  | ModeHtml
  | ModeMake
  deriving Eq

-- |Type of the target file
data TargetType
  = Parsed                -- ^ Parsed source code
  | FlatCurry             -- ^ FlatCurry
  | ExtendedFlatCurry     -- ^ Extended FlatCurry
  | FlatXml               -- ^ FlatCurry as XML
  | AbstractCurry         -- ^ AbstractCurry
  | UntypedAbstractCurry  -- ^ UntypedAbstractCurry
    deriving Eq

-- |Data type representing the verbosity level
data Verbosity
  = VerbQuiet  -- ^ be queit
  | VerbStatus -- ^ show status of compilation
  | VerbInfo   -- ^ show also additional info
    deriving (Eq, Ord)

-- |Classifies a number as a 'Verbosity'
classifyVerbosity :: String -> Verbosity -> Verbosity
classifyVerbosity "0" _ = VerbQuiet
classifyVerbosity "1" _ = VerbStatus
classifyVerbosity "2" _ = VerbInfo
classifyVerbosity _   v = v

-- |Data type for representing code dumps
data DumpLevel
  = DumpRenamed      -- ^ dump source  after renaming
  | DumpDesugared    -- ^ dump source  after desugaring
  | DumpSimplified   -- ^ dump source  after simplification
  | DumpLifted       -- ^ dump source  after lambda-lifting
  | DumpIL           -- ^ dump IL code after translation
  | DumpCase         -- ^ dump IL code after case completion
    deriving (Eq, Bounded, Enum, Show)

-- |All available 'DumpLevel's
dumpAll :: [DumpLevel]
dumpAll = [minBound .. maxBound]

-- |Data type representing language extensions
data Extension
  = Records
  | FunctionalPatterns
  | AnonFreeVars
  | NoImplicitPrelude
  | UnknownExtension String
    deriving (Eq, Read, Show)

allExtensions :: [Extension]
allExtensions = [Records, FunctionalPatterns, AnonFreeVars, NoImplicitPrelude]

-- |'Extension's available by @-e@ flag
curryExtensions :: [Extension]
curryExtensions = [Records, FunctionalPatterns, AnonFreeVars]

-- |Classifies a 'String' as an 'Extension'
classifyExtension :: String -> Extension
classifyExtension str = case reads str of
  [(e, "")] -> e
  _         -> UnknownExtension str

-- | All available compiler options
options :: [OptDescr (Options -> Options)]
options =
  -- modus operandi
  [ Option "h?" ["help"]
      (NoArg (\ opts -> opts { optMode = ModeHelp }))
      "display this help and exit"
  , Option "V"  ["version"]
      (NoArg (\ opts -> opts { optMode = ModeVersion }))
      "show the version number and exit"
  , Option ""   ["numeric-version"]
      (NoArg (\ opts -> opts { optMode = ModeNumericVersion }))
      "show the numeric version number and exit"
  , Option ""   ["html"]
      (NoArg (\ opts -> opts { optMode = ModeHtml }))
      "generate html code and exit"
  -- verbosity
  , Option "v"  ["verbosity"]
      (ReqArg (\ arg opts -> opts { optVerbosity =
        classifyVerbosity arg $ optVerbosity opts}) "<n>")
      "set verbosity level to <n>, one of 0 = quiet, 1 = status, 2 = info"
  , Option "" ["no-verb"]
      (NoArg (\ opts -> opts { optVerbosity = VerbQuiet } ))
      "set verbosity level to quiet"
  -- compilation
  , Option "f"  ["force"]
      (NoArg (\ opts -> opts { optForce = True }))
      "force compilation of target file"
  , Option "P"  ["lib-dir"]
      (ReqArg (\ arg opts -> opts { optLibraryPaths =
        nub $ optLibraryPaths opts ++ splitSearchPath arg}) "dir:dir2:...")
      "search for librares in dir:dir2:..."
  , Option "i"  ["import-dir"]
      (ReqArg (\ arg opts -> opts { optImportPaths =
        nub $ optImportPaths opts ++ splitSearchPath arg}) "dir:dir2:...")
      "search for imports in dir:dir2:..."
  , Option "o"  ["output"]
      (ReqArg (\ arg opts -> opts { optOutput = Just arg }) "FILE")
      "write code to FILE"
  , Option ""   ["no-subdir"]
      (NoArg (\ opts -> opts { optUseSubdir = False }))
      ("disable writing to '" ++ currySubdir ++ "' subdirectory")
  , Option ""   ["no-intf"]
      (NoArg (\ opts -> opts { optInterface = False }))
      "do not create an interface file"
  , Option ""   ["no-warn"]
      (NoArg (\ opts -> opts { optWarn = False }))
      "do not print warnings"
  , Option ""   ["no-overlap-warn"]
      (NoArg (\ opts -> opts { optOverlapWarn = False }))
      "do not print warnings for overlapping rules"
  -- target types
  , Option ""   ["parse-only"]
      (NoArg (\ opts -> opts { optTargetTypes =
        nub $ Parsed : optTargetTypes opts }))
      "generate source representation"
  , Option ""   ["flat"]
      (NoArg (\ opts -> opts { optTargetTypes =
        nub $ FlatCurry : optTargetTypes opts }))
      "generate FlatCurry code"
  , Option ""   ["extended-flat"]
      (NoArg (\ opts -> opts { optTargetTypes =
        nub $ ExtendedFlatCurry : optTargetTypes opts }))
      "generate FlatCurry code with source references"
  , Option ""   ["xml"]
      (NoArg (\ opts -> opts { optTargetTypes =
        nub $ FlatXml : optTargetTypes opts }))
      "generate flat xml code"
  , Option ""   ["acy"]
      (NoArg (\ opts -> opts { optTargetTypes =
        nub $ AbstractCurry : optTargetTypes opts }))
      "generate (type infered) AbstractCurry code"
  , Option ""   ["uacy"]
      (NoArg (\ opts -> opts { optTargetTypes =
        nub $ UntypedAbstractCurry : optTargetTypes opts }))
      "generate untyped AbstractCurry code"
  -- extensions
  , Option "e"  ["extended"]
      (NoArg (\ opts -> opts { optExtensions =
        nub $ curryExtensions ++ optExtensions opts }))
      "enable extended Curry functionalities"
  , Option "X"   []
      (ReqArg (\ arg opts -> opts { optExtensions =
        nub $ classifyExtension arg : optExtensions opts }) "EXT")
      ("enable language extension EXT, one of " ++ show allExtensions)
  -- dump
  , Option ""   ["dump-all"]
      (NoArg (\ opts -> opts { optDumps = dumpAll }))
      "dump everything"
  , Option ""   ["dump-renamed"]
      (NoArg (\ opts -> opts { optDumps =
        nub $ DumpRenamed : optDumps opts }))
      "dump source code after renaming"
  , Option ""   ["dump-desugared"]
      (NoArg (\ opts -> opts { optDumps =
        nub $ DumpDesugared : optDumps opts }))
      "dump source code after desugaring"
  , Option ""   ["dump-simplified"]
      (NoArg (\ opts -> opts { optDumps = nub $
        DumpSimplified : optDumps opts }))
      "dump source code after simplification"
  , Option ""   ["dump-lifted"]
      (NoArg (\ opts -> opts { optDumps = nub $ DumpLifted : optDumps opts }))
      "dump source code after lambda-lifting"
  , Option ""   ["dump-il"]
      (NoArg (\ opts -> opts { optDumps = nub $ DumpIL : optDumps opts }))
      "dump intermediate language before lifting"
  , Option ""   ["dump-case"]
      (NoArg (\ opts -> opts { optDumps = nub $ DumpCase : optDumps opts }))
      "dump intermediate language after case simplification"
  ]

-- |Parse the command line arguments
parseOpts :: [String] -> (Options, [String], [String])
parseOpts args = (foldl (flip ($)) defaultOptions opts, files, errs) where
  (opts, files, errs) = getOpt Permute options args

-- |Check options and files and return a list of error messages
checkOpts :: Options -> [String] -> [String]
checkOpts opts files
  | isJust (optOutput opts) && length files > 1
  = ["cannot specify -o with multiple targets"]
  | not $ null unknownExtensions
  = ["Unknown language extension(s): " ++ intercalate ", " unknownExtensions]
  | otherwise
  = []
  where unknownExtensions = [ e | UnknownExtension e <- optExtensions opts ]

-- |Print the usage information of the command line tool.
usage :: String -> String
usage prog = usageInfo header options
  where header = "usage: " ++ prog ++ " [OPTION] ... MODULE ..."

-- |Retrieve the compiler 'Options'
compilerOpts :: IO (String, Options, [String], [String])
compilerOpts = do
  args <- getArgs
  prog <- getProgName
  let (opts, files, errs) = parseOpts args
  return (prog, opts, files, errs ++ checkOpts opts files)
