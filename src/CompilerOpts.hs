{- |
    Module      :  $Header$
    Description :  Compiler options
    Copyright   :  (c) 2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2013 Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines data structures holding options for the
    compilation of Curry programs, and utility functions for printing
    help information as well as parsing the cmd arguments.
-}
module CompilerOpts
  ( Options (..), CymakeMode (..), Verbosity (..), TargetType (..)
  , WarnFlag (..), Extension (..), DumpLevel (..), dumpLevel
  , defaultOptions, getCompilerOpts, usage
  ) where

import Data.List             (intercalate, nub)
import Data.Maybe            (isJust)
import System.Console.GetOpt
import System.Environment    (getArgs, getProgName)
import System.FilePath       (splitSearchPath)

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
  , optWarnFlags    :: [WarnFlag]
  , optWarnAsError  :: Bool
  , optTargetTypes  :: [TargetType]   -- ^ what to generate
  , optExtensions   :: [Extension]    -- ^ enabled language extensions
  , optDumps        :: [DumpLevel]    -- ^ dump levels
  , optDumpEnv      :: Bool           -- ^ dump compilation environment
  , optDumpRaw      :: Bool           -- ^ dump data structure
  } deriving Show

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
  , optWarnFlags    = [minBound .. maxBound]
  , optWarnAsError  = False
  , optTargetTypes  = []
  , optExtensions   = []
  , optDumps        = []
  , optDumpEnv      = False
  , optDumpRaw      = False
  }

-- |Modus operand of the program
data CymakeMode
  = ModeHelp           -- ^ Show help information
  | ModeVersion        -- ^ Show version
  | ModeNumericVersion -- ^ Show only version, suitable for later processing
  | ModeHtml           -- ^ Create HTML documentation
  | ModeMake           -- ^ Compile with dependencies
  deriving (Eq, Show)

-- |Data type representing the verbosity level
data Verbosity
  = VerbQuiet  -- ^ be quiet
  | VerbStatus -- ^ show status of compilation
  | VerbInfo   -- ^ show also additional info
    deriving (Eq, Ord, Show)

-- |Type of the target file
data TargetType
  = Parsed                -- ^ Parsed source code
  | FlatCurry             -- ^ FlatCurry
  | ExtendedFlatCurry     -- ^ Extended FlatCurry
  | FlatXml               -- ^ FlatCurry as XML
  | AbstractCurry         -- ^ AbstractCurry
  | UntypedAbstractCurry  -- ^ Untyped AbstractCurry
    deriving (Eq, Show)

-- |Warnings flags
data WarnFlag
  = WarnMultipleImports    -- ^ Warn for multiple imports
  | WarnDisjoinedRules     -- ^ Warn for disjoined function rules
  | WarnUnusedBindings     -- ^ Warn for unused bindings
  | WarnNameShadowing      -- ^ Warn for name shadowing
  | WarnOverlapping        -- ^ Warn for overlapping rules/alternatives
  | WarnIncompletePatterns -- ^ Warn for incomplete pattern matching
  | WarnIdleAlternatives   -- ^ Warn for idle case alternatives
    deriving (Eq, Bounded, Enum, Show)

warnFlags :: [(WarnFlag, String, String)]
warnFlags =
  [ (WarnMultipleImports   , "multiple-imports"   , "multiple imports"           )
  , (WarnDisjoinedRules    , "disjoined-rules"    , "disjoined function rules"   )
  , (WarnUnusedBindings    , "unused-bindings"    , "unused bindings"            )
  , (WarnNameShadowing     , "name-shadowing"     , "name shadowing"             )
  , (WarnOverlapping       , "overlapping"        , "overlapping function rules" )
  , (WarnIncompletePatterns, "incomplete-patterns", "incomplete pattern matching")
  , (WarnIdleAlternatives  , "idle-alternatives"  , "idle case alternatives"     )
  ]

-- |Data type for representing code dumps
data DumpLevel
  = DumpParsed        -- ^ dump source code after parsing
  | DumpKindChecked   -- ^ dump source code after kind checking
  | DumpSyntaxChecked -- ^ dump source code after syntax checking
  | DumpPrecChecked   -- ^ dump source code after precedence checking
  | DumpTypeChecked   -- ^ dump source code after type checking
  | DumpQualified     -- ^ dump source  after qualification
  | DumpDesugared     -- ^ dump source  after desugaring
  | DumpSimplified    -- ^ dump source  after simplification
  | DumpLifted        -- ^ dump source  after lambda-lifting
  | DumpTranslated    -- ^ dump IL code after translation
  | DumpCaseCompleted -- ^ dump IL code after case completion
    deriving (Eq, Bounded, Enum, Show)

dumpLevel :: [(DumpLevel, String, String)]
dumpLevel = [ (DumpParsed       , "parsed", "parse tree"               )
            , (DumpKindChecked  , "kc"    , "kind checker output"      )
            , (DumpSyntaxChecked, "sc"    , "syntax checker output"    )
            , (DumpPrecChecked  , "pc"    , "precedence checker output")
            , (DumpTypeChecked  , "tc"    , "type checker output"      )
            , (DumpQualified    , "qual"  , "qualifier output"         )
            , (DumpDesugared    , "ds"    , "desugarer output"         )
            , (DumpSimplified   , "simpl" , "simplifier output"        )
            , (DumpLifted       , "lifted", "lifting output"           )
            , (DumpTranslated   , "trans" , "translated output"        )
            , (DumpCaseCompleted, "cc"    , "case completed output"    )
            ]

-- |Data type representing language extensions
data Extension
  = Records
  | FunctionalPatterns
  | AnonFreeVars
  | NoImplicitPrelude
    deriving (Eq, Read, Show)

allExtensions :: [Extension]
allExtensions = [Records, FunctionalPatterns, AnonFreeVars, NoImplicitPrelude]

-- |'Extension's available by @-e@ flag
curryExtensions :: [Extension]
curryExtensions = [Records, FunctionalPatterns, AnonFreeVars]

type OptErr = (Options, [String])

onOpts :: (Options -> Options) -> OptErr -> OptErr
onOpts f (opts, errs) = (f opts, errs)

onOptsArg :: (String -> Options -> Options) -> String -> OptErr -> OptErr
onOptsArg f arg (opts, errs) = (f arg opts, errs)

addErr :: String -> OptErr -> OptErr
addErr err (opts, errs) = (opts, errs ++ [err])

-- | All available compiler options
options :: [OptDescr (OptErr -> OptErr)]
options =
  -- modus operandi
  [ Option "h?" ["help"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeHelp }))
      "display this help and exit"
  , Option "V"  ["version"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeVersion }))
      "show the version number and exit"
  , Option ""   ["numeric-version"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeNumericVersion }))
      "show the numeric version number and exit"
  , Option ""   ["html"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeHtml }))
      "generate html code and exit"
  -- verbosity
  , Option "v"  ["verbosity"]
      (ReqArg parseVerbosity "n")
      ("set verbosity level to `n', where `n' is one of\n"
        ++ "  0: quiet\n  1: status\n  2: info")
    -- legacy
  , Option "q"  ["no-verb"]
      (NoArg (onOpts $ \ opts -> opts { optVerbosity = VerbQuiet } ))
      "set verbosity level to quiet"
  -- compilation
  , Option "f"  ["force"]
      (NoArg (onOpts $ \ opts -> opts { optForce = True }))
      "force compilation of target file"
  , Option "P"  ["lib-dir"]
      (ReqArg (onOptsArg $ \ arg opts -> opts { optLibraryPaths =
        nub $ optLibraryPaths opts ++ splitSearchPath arg}) "dir[:dir]")
      "search for libraries in dir[:dir]"
  , Option "i"  ["import-dir"]
      (ReqArg (onOptsArg $ \ arg opts -> opts { optImportPaths =
        nub $ optImportPaths opts ++ splitSearchPath arg}) "dir[:dir]")
      "search for imports in dir[:dir]"
  , Option "o"  ["output"]
      (ReqArg (onOptsArg $ \ arg opts -> opts { optOutput = Just arg }) "file")
      "write code to `file'"
  , Option ""   ["no-subdir"]
      (NoArg (onOpts $ \ opts -> opts { optUseSubdir = False }))
      ("disable writing to `" ++ currySubdir ++ "' subdirectory")
  , Option ""   ["no-intf"]
      (NoArg (onOpts $ \ opts -> opts { optInterface = False }))
      "do not create an interface file"
  , Option ""   ["no-warn"]
      (NoArg (onOpts $ \ opts -> opts { optWarn = False }))
      "do not print warnings"
    -- legacy
  , Option ""   ["no-overlap-warn"]
      (NoArg (onOpts $ \ opts -> opts { optWarnFlags =
          addFlag WarnOverlapping (optWarnFlags opts) }))
      "do not print warnings for overlapping rules"
  -- target types
  , Option ""   ["parse-only"]
      (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
        nub $ Parsed : optTargetTypes opts }))
      "generate source representation"
  , Option ""   ["flat"]
      (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
        nub $ FlatCurry : optTargetTypes opts }))
      "generate FlatCurry code"
  , Option ""   ["extended-flat"]
      (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
        nub $ ExtendedFlatCurry : optTargetTypes opts }))
      "generate FlatCurry code with source references"
  , Option ""   ["xml"]
      (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
        nub $ FlatXml : optTargetTypes opts }))
      "generate flat xml code"
  , Option ""   ["acy"]
      (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
        nub $ AbstractCurry : optTargetTypes opts }))
      "generate (type infered) AbstractCurry code"
  , Option ""   ["uacy"]
      (NoArg (onOpts $ \ opts -> opts { optTargetTypes =
        nub $ UntypedAbstractCurry : optTargetTypes opts }))
      "generate untyped AbstractCurry code"
  -- extensions
  , Option "e"  ["extended"]
      (NoArg (onOpts $ \ opts -> opts { optExtensions =
        nub $ curryExtensions ++ optExtensions opts }))
      "enable extended Curry functionalities"
  , Option "X"   []
      (ReqArg parseLanguageExtension "ext")
      ("enable language extension `ext', where `ext' is one of\n"
      ++ intercalate "\n" (map (\e -> "  " ++ show e) allExtensions))
  , Option "W"   ["warning"]
      (ReqArg parseWarnOption "opt")
      ("set warning option `opt', where `opt' ist one of\n"
        ++ renderDescriptions warnDescriptions)
  , Option "d"   ["dump"]
      (ReqArg parseDumpOption "opt")
      ("set dump option `opt', where `opt' ist one of\n"
        ++ renderDescriptions dumpDescriptions)
  ]

-- |Classifies a number as a 'Verbosity'
parseVerbosity :: String -> OptErr -> OptErr
parseVerbosity "0" = onOpts $ \ opts -> opts { optVerbosity =  VerbQuiet  }
parseVerbosity "1" = onOpts $ \ opts -> opts { optVerbosity =  VerbStatus }
parseVerbosity "2" = onOpts $ \ opts -> opts { optVerbosity =  VerbInfo   }
parseVerbosity opt = addErr $ "illegal verbosity `" ++ opt ++ "'\n"

parseLanguageExtension :: String -> OptErr -> OptErr
parseLanguageExtension opt = case reads opt of
  [(ext, "")] -> onOpts (addExt ext)
  _           -> addErr $ "unrecognized language extension `" ++ opt ++ "'\n"
  where
  addExt e = \opts -> opts { optExtensions = addFlag e (optExtensions opts) }

parseWarnOption :: String -> OptErr -> OptErr
parseWarnOption opt = case lookup3 opt warnDescriptions of
  Just f  -> onOpts f
  Nothing -> addErr $ "unrecognized warning option `" ++ opt ++ "'\n"

renderDescriptions :: [(String, String, Options -> Options)] -> String
renderDescriptions ds
  = intercalate "\n" $ map (\(k, d, _) -> "  " ++ rpad maxLen k ++ ": " ++ d) ds
  where
  maxLen = maximum $ map (\(k, _, _) -> length k) ds
  rpad n x = x ++ replicate (n - length x) ' '

warnDescriptions :: [(String, String, Options -> Options)]
warnDescriptions
  = [ ( "all"  , "turn on all warnings"
        , \ opts -> opts { optWarnFlags = [minBound .. maxBound] } )
    , ("none" , "turn off all warnings"
        , \ opts -> opts { optWarnFlags = []                     } )
    , ("error", "treat warnings as errors"
        , \ opts -> opts { optWarnAsError = True                 } )
    ] ++ map turnOn warnFlags ++ map turnOff warnFlags
  where
  turnOn (flag, name, desc)
    = (name, "warn for " ++ desc
      , \ opts -> opts { optWarnFlags = addFlag flag (optWarnFlags opts)})
  turnOff (flag, name, desc)
    = ("no-" ++ name, "do not warn for " ++ desc
      , \ opts -> opts { optWarnFlags = removeFlag flag (optWarnFlags opts)})

parseDumpOption :: String -> OptErr -> OptErr
parseDumpOption opt = case lookup3 opt dumpDescriptions of
  Just f  -> onOpts f
  Nothing -> addErr $ "unrecognized dump option `" ++ opt ++ "'"

dumpDescriptions :: [(String, String, Options -> Options)]
dumpDescriptions =
  [ ( "all", "dump everything"
    , \ opts -> opts { optDumps = [minBound .. maxBound] })
  , ( "none", "dump nothing"
    , \ opts -> opts { optDumps = []                     })
  , ( "env" , "additionally dump compiler environment"
    , \ opts -> opts { optDumpEnv = True                 })
  , ( "raw" , "dump as raw AST (instead of pretty printed)"
    , \ opts -> opts { optDumpRaw = True                 })
  ] ++ map toDescr dumpLevel
  where
  toDescr (flag, name, desc)
    = (name , "dump " ++ desc
        , \ opts -> opts { optDumps = addFlag flag (optDumps opts)})

addFlag :: Eq a => a -> [a] -> [a]
addFlag o opts = nub $ o : opts

removeFlag :: Eq a => a -> [a] -> [a]
removeFlag o opts = filter (/= o) opts

lookup3 :: Eq a => a -> [(a, b, c)] -> Maybe c
lookup3 _ []                  = Nothing
lookup3 k ((k', _, v2) : kvs)
  | k == k'                   = Just v2
  | otherwise                 = lookup3 k kvs

-- |Parse the command line arguments
parseOpts :: [String] -> (Options, [String], [String])
parseOpts args = (opts, files, errs ++ errs2)
  where
  (opts, errs2) = foldl (flip ($)) (defaultOptions, []) optErrs
  (optErrs, files, errs) = getOpt Permute options args

-- |Check options and files and return a list of error messages
checkOpts :: Options -> [String] -> [String]
checkOpts opts files
  | isJust (optOutput opts) && length files > 1
  = ["cannot specify -o with multiple targets"]
  | otherwise
  = []

-- |Print the usage information of the command line tool.
usage :: String -> String
usage prog = usageInfo header options
  where header = "usage: " ++ prog ++ " [OPTION] ... MODULES ..."

-- |Retrieve the compiler 'Options'
getCompilerOpts :: IO (String, Options, [String], [String])
getCompilerOpts = do
  args <- getArgs
  prog <- getProgName
  let (opts, files, errs) = parseOpts args
  return (prog, opts, files, errs ++ checkOpts opts files)
