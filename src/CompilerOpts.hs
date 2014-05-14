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
    help information as well as parsing the command line arguments.
-}
module CompilerOpts
  ( Options (..), PrepOpts (..), WarnOpts (..), DebugOpts (..)
  , CymakeMode (..), Verbosity (..), TargetType (..)
  , WarnFlag (..), KnownExtension (..), DumpLevel (..), dumpLevel
  , defaultOptions, defaultPrepOpts, defaultWarnOpts, defaultDebugOpts
  , getCompilerOpts, usage
  ) where

import Data.List             (intercalate, nub)
import Data.Maybe            (isJust)
import System.Console.GetOpt
import System.Environment    (getArgs, getProgName)
import System.FilePath       (splitSearchPath)

import Curry.Files.Filenames (currySubdir)
import Curry.Syntax.Extension

-- -----------------------------------------------------------------------------
-- Option data structures
-- -----------------------------------------------------------------------------

-- |Compiler options
data Options = Options
  -- general
  { optMode         :: CymakeMode       -- ^ modus operandi
  , optVerbosity    :: Verbosity        -- ^ verbosity level
  -- compilation
  , optForce        :: Bool             -- ^ force (re-)compilation of target
  , optLibraryPaths :: [FilePath]       -- ^ directories to search in
                                        --   for libraries
  , optImportPaths  :: [FilePath]       -- ^ directories to search in
                                        --   for imports
  , optHtmlDir      :: Maybe FilePath   -- ^ output directory for HTML
  , optUseSubdir    :: Bool             -- ^ use subdir for output?
  , optInterface    :: Bool             -- ^ create a FlatCurry interface file?
  , optPrepOpts     :: PrepOpts         -- ^ preprocessor options
  , optWarnOpts     :: WarnOpts         -- ^ warning options
  , optTargetTypes  :: [TargetType]     -- ^ what to generate
  , optExtensions   :: [KnownExtension] -- ^ enabled language extensions
  , optDebugOpts    :: DebugOpts        -- ^ debug options
  } deriving Show

-- |Preprocessor options
data PrepOpts = PrepOpts
  { ppPreprocess :: Bool      -- ^ apply custom preprocessor
  , ppCmd        :: String    -- ^ preprocessor command
  , ppOpts       :: [String]  -- ^ preprocessor options
  } deriving Show

-- |Warning options
data WarnOpts = WarnOpts
  { wnWarn         :: Bool       -- ^ show warnings? (legacy option)
  , wnWarnFlags    :: [WarnFlag] -- ^ Warnings flags (see below)
  , wnWarnAsError  :: Bool       -- ^ Should warnings be treated as errors?
  } deriving Show

-- |Debug options
data DebugOpts = DebugOpts
  { dbDumpLevels :: [DumpLevel] -- ^ dump levels
  , dbDumpEnv :: Bool           -- ^ dump compilation environment
  , dbDumpRaw :: Bool           -- ^ dump data structure
  } deriving Show

-- | Default compiler options
defaultOptions :: Options
defaultOptions = Options
  { optMode         = ModeMake
  , optVerbosity    = VerbStatus
  , optForce        = False
  , optLibraryPaths = []
  , optImportPaths  = []
  , optHtmlDir      = Nothing
  , optUseSubdir    = True
  , optInterface    = True
  , optPrepOpts     = defaultPrepOpts
  , optWarnOpts     = defaultWarnOpts
  , optTargetTypes  = []
  , optExtensions   = []
  , optDebugOpts    = defaultDebugOpts
  }

-- | Default preprocessor options
defaultPrepOpts :: PrepOpts
defaultPrepOpts = PrepOpts
  { ppPreprocess = False
  , ppCmd        = ""
  , ppOpts       = []
  }

-- | Default warning options
defaultWarnOpts :: WarnOpts
defaultWarnOpts = WarnOpts
  { wnWarn        = True
  , wnWarnFlags   = stdWarnFlags
  , wnWarnAsError = False
  }

-- | Default dump options
defaultDebugOpts :: DebugOpts
defaultDebugOpts = DebugOpts
  { dbDumpLevels = []
  , dbDumpEnv    = False
  , dbDumpRaw    = False
  }

-- |Modus operandi of the program
data CymakeMode
  = ModeHelp           -- ^ Show help information and exit
  | ModeVersion        -- ^ Show version and exit
  | ModeNumericVersion -- ^ Show numeric version, suitable for later processing
  | ModeHtml           -- ^ Create HTML documentation
  | ModeMake           -- ^ Compile with dependencies
  deriving (Eq, Show)

-- |Verbosity level
data Verbosity
  = VerbQuiet  -- ^ be quiet
  | VerbStatus -- ^ show status of compilation
  deriving (Eq, Ord, Show)

-- |Description and flag of verbosities
verbosities :: [(Verbosity, String, String)]
verbosities = [ ( VerbQuiet , "0", "quiet" )
              , ( VerbStatus, "1", "status")
              ]

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

-- |Warning flags enabled by default
stdWarnFlags :: [WarnFlag]
stdWarnFlags =
  [ WarnMultipleImports , WarnDisjoinedRules, WarnUnusedBindings
  , WarnNameShadowing   , WarnOverlapping -- , WarnIncompletePatterns
  , WarnIdleAlternatives
  ]

-- |Description and flag of warnings flags
warnFlags :: [(WarnFlag, String, String)]
warnFlags =
  [ ( WarnMultipleImports   , "multiple-imports"
    , "multiple imports"           )
  , ( WarnDisjoinedRules    , "disjoined-rules"
    , "disjoined function rules"   )
  , ( WarnUnusedBindings    , "unused-bindings"
    , "unused bindings"            )
  , ( WarnNameShadowing     , "name-shadowing"
    , "name shadowing"             )
  , ( WarnOverlapping       , "overlapping"
    , "overlapping function rules" )
  , ( WarnIncompletePatterns, "incomplete-patterns"
    , "incomplete pattern matching")
  , ( WarnIdleAlternatives  , "idle-alternatives"
    , "idle case alternatives"     )
  ]

-- |Dump level
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

-- |Description and flag of dump levels
dumpLevel :: [(DumpLevel, String, String)]
dumpLevel = [ (DumpParsed       , "dump-parse", "parse tree"               )
            , (DumpKindChecked  , "dump-kc"   , "kind checker output"      )
            , (DumpSyntaxChecked, "dump-sc"   , "syntax checker output"    )
            , (DumpPrecChecked  , "dump-pc"   , "precedence checker output")
            , (DumpTypeChecked  , "dump-tc"   , "type checker output"      )
            , (DumpQualified    , "dump-qual" , "qualifier output"         )
            , (DumpDesugared    , "dump-ds"   , "desugarer output"         )
            , (DumpSimplified   , "dump-simpl", "simplifier output"        )
            , (DumpLifted       , "dump-lift" , "lifting output"           )
            , (DumpTranslated   , "dump-trans", "translated output"        )
            , (DumpCaseCompleted, "dump-cc"   , "case completed output"    )
            ]

-- |Description and flag of language extensions
extensions :: [(KnownExtension, String, String)]
extensions =
  [ ( AnonFreeVars      , "AnonFreeVars"
    , "enable anonymous free variables"     )
  , ( FunctionalPatterns, "FunctionalPatterns"
    , "enable functional patterns"          )
  , ( NoImplicitPrelude , "NoImplicitPrelude"
    , "do not implicitly import the Prelude")
  , ( Records           , "Records"
    , "enable record syntax"                )
  ]

-- -----------------------------------------------------------------------------
-- Parsing of the command line options.
--
-- Because some flags require additional arguments, the structure is slightly
-- more complicated to enable malformed arguments to be reported.
-- -----------------------------------------------------------------------------

-- |Instead of just returning the resulting 'Options' structure, we also
-- collect errors from arguments passed to specific options.
type OptErr = (Options, [String])

-- |An 'OptErrTable' consists of a list of entries of the following form:
--   * a flag to be recognized on the command line
--   * an explanation text for the usage information
--   * a modification funtion adjusting the options structure
-- The type is parametric about the option's type to adjust.
type OptErrTable opt = [(String, String, opt -> opt)]

onOpts :: (Options -> Options) -> OptErr -> OptErr
onOpts f (opts, errs) = (f opts, errs)

onPrepOpts :: (PrepOpts -> PrepOpts) -> OptErr -> OptErr
onPrepOpts f (opts, errs) = (opts { optPrepOpts = f (optPrepOpts opts) }, errs)

onWarnOpts :: (WarnOpts -> WarnOpts) -> OptErr -> OptErr
onWarnOpts f (opts, errs) = (opts { optWarnOpts = f (optWarnOpts opts) }, errs)

onDebugOpts :: (DebugOpts -> DebugOpts) -> OptErr -> OptErr
onDebugOpts f (opts, errs)
  = (opts { optDebugOpts = f (optDebugOpts opts) }, errs)

withArg :: ((opt -> opt) -> OptErr -> OptErr)
        -> (String -> opt -> opt) -> String -> OptErr -> OptErr
withArg lift f arg = lift (f arg)

addErr :: String -> OptErr -> OptErr
addErr err (opts, errs) = (opts, errs ++ [err])

mkOptDescr :: ((opt -> opt) -> OptErr -> OptErr)
           -> String -> [String] -> String -> String -> OptErrTable opt
           -> OptDescr (OptErr -> OptErr)
mkOptDescr lift flags longFlags arg what tbl = Option flags longFlags
  (ReqArg (parseOptErr lift what tbl) arg)
  ("set " ++ what ++ " `" ++ arg ++ "', where `" ++ arg ++ "' is one of\n"
    ++ renderOptErrTable tbl)

parseOptErr :: ((opt -> opt) -> OptErr -> OptErr)
            -> String -> OptErrTable opt -> String -> OptErr -> OptErr
parseOptErr lift what table opt = case lookup3 opt table of
  Just f  -> lift f
  Nothing -> addErr $ "unrecognized " ++ what ++ '`' : opt ++ "'\n"
  where
  lookup3 _ []                  = Nothing
  lookup3 k ((k', _, v2) : kvs)
    | k == k'                   = Just v2
    | otherwise                 = lookup3 k kvs

renderOptErrTable :: OptErrTable opt -> String
renderOptErrTable ds
  = intercalate "\n" $ map (\(k, d, _) -> "  " ++ rpad maxLen k ++ ": " ++ d) ds
  where
  maxLen = maximum $ map (\(k, _, _) -> length k) ds
  rpad n x = x ++ replicate (n - length x) ' '

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
  -- verbosity
  , mkOptDescr onOpts "v" ["verbosity"] "n" "verbosity level" verbDescriptions
  , Option "q"  ["no-verb"]
      (NoArg (onOpts $ \ opts -> opts { optVerbosity = VerbQuiet } ))
      "set verbosity level to quiet"
  -- compilation
  , Option "f"  ["force"]
      (NoArg (onOpts $ \ opts -> opts { optForce = True }))
      "force compilation of target file"
  , Option "P"  ["lib-dir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optLibraryPaths =
        nub $ optLibraryPaths opts ++ splitSearchPath arg}) "dir[:dir]")
      "search for libraries in dir[:dir]"
  , Option "i"  ["import-dir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optImportPaths =
        nub $ optImportPaths opts ++ splitSearchPath arg}) "dir[:dir]")
      "search for imports in dir[:dir]"
  , Option []  ["htmldir"]
      (ReqArg (withArg onOpts $ \ arg opts -> opts { optHtmlDir =
        Just arg }) "dir")
      "write HTML documentation into directory `dir'"
  , Option ""   ["no-subdir"]
      (NoArg (onOpts $ \ opts -> opts { optUseSubdir = False }))
      ("disable writing to `" ++ currySubdir ++ "' subdirectory")
  , Option ""   ["no-intf"]
      (NoArg (onOpts $ \ opts -> opts { optInterface = False }))
      "do not create an interface file"
    -- legacy warning flags
  , Option ""   ["no-warn"]
      (NoArg (onWarnOpts $ \ opts -> opts { wnWarn = False }))
      "do not print warnings"
  , Option ""   ["no-overlap-warn"]
      (NoArg (onWarnOpts $ \ opts -> opts {wnWarnFlags =
        addFlag WarnOverlapping (wnWarnFlags opts) }))
      "do not print warnings for overlapping rules"
  -- target types
  , Option ""   ["html"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeHtml }))
      "generate html code and exit"
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
  , Option "F"  []
      (NoArg (onPrepOpts $ \ opts -> opts { ppPreprocess = True }))
      "use custom preprocessor"
  , Option ""   ["pgmF"]
      (ReqArg (withArg onPrepOpts $ \ arg opts -> opts { ppCmd = arg})
        "cmd")
      "execute preprocessor command <cmd>"
  , Option ""   ["optF"]
      (ReqArg (withArg onPrepOpts $ \ arg opts ->
        opts { ppOpts = ppOpts opts ++ [arg]}) "option")
      "execute preprocessor with option <option>"
  -- extensions
  , Option "e"  ["extended"]
      (NoArg (onOpts $ \ opts -> opts { optExtensions =
        nub $ kielExtensions ++ optExtensions opts }))
      "enable extended Curry functionalities"
  , mkOptDescr onOpts      "X" [] "ext" "language extension" extDescriptions
  , mkOptDescr onWarnOpts  "W" [] "opt" "warning option"     warnDescriptions
  , mkOptDescr onDebugOpts "d" [] "opt" "debug option"       debugDescriptions
  ]

verbDescriptions :: OptErrTable Options
verbDescriptions = map toDescr verbosities
  where
  toDescr (flag, name, desc)
    = (name, desc, \ opts -> opts { optVerbosity = flag })

extDescriptions :: OptErrTable Options
extDescriptions = map toDescr extensions
  where
  toDescr (flag, name, desc)
    = (name, desc,
        \ opts -> opts { optExtensions = addFlag flag (optExtensions opts)})

warnDescriptions :: OptErrTable WarnOpts
warnDescriptions
  = [ ( "all"  , "turn on all warnings"
        , \ opts -> opts { wnWarnFlags = [minBound .. maxBound] } )
    , ("none" , "turn off all warnings"
        , \ opts -> opts { wnWarnFlags = []                     } )
    , ("error", "treat warnings as errors"
        , \ opts -> opts { wnWarnAsError = True                 } )
    ] ++ map turnOn warnFlags ++ map turnOff warnFlags
  where
  turnOn (flag, name, desc)
    = (name, "warn for " ++ desc
      , \ opts -> opts { wnWarnFlags = addFlag flag (wnWarnFlags opts)})
  turnOff (flag, name, desc)
    = ("no-" ++ name, "do not warn for " ++ desc
      , \ opts -> opts { wnWarnFlags = removeFlag flag (wnWarnFlags opts)})

debugDescriptions :: OptErrTable DebugOpts
debugDescriptions =
  [ ( "dump-all", "dump everything"
    , \ opts -> opts { dbDumpLevels = [minBound .. maxBound] })
  , ( "dump-none", "dump nothing"
    , \ opts -> opts { dbDumpLevels = []                     })
  , ( "dump-env" , "additionally dump compiler environment"
    , \ opts -> opts { dbDumpEnv = True                 })
  , ( "dump-raw" , "dump as raw AST (instead of pretty printed)"
    , \ opts -> opts { dbDumpRaw = True                 })
  ] ++ map toDescr dumpLevel
  where
  toDescr (flag, name, desc)
    = (name , "dump " ++ desc
        , \ opts -> opts { dbDumpLevels = addFlag flag (dbDumpLevels opts)})

addFlag :: Eq a => a -> [a] -> [a]
addFlag o opts = nub $ o : opts

removeFlag :: Eq a => a -> [a] -> [a]
removeFlag o opts = filter (/= o) opts

-- |Parse the command line arguments
parseOpts :: [String] -> (Options, [String], [String])
parseOpts args = (opts, files, errs ++ errs2 ++ checkOpts opts files)
  where
  (opts, errs2) = foldl (flip ($)) (defaultOptions, []) optErrs
  (optErrs, files, errs) = getOpt Permute options args

-- |Check options and files and return a list of error messages
checkOpts :: Options -> [String] -> [String]
checkOpts opts _
  | isJust (optHtmlDir opts) && (optMode opts) /= ModeHtml
  = ["The option '--htmldir' is only valid for HTML generation mode"]
  | otherwise = []

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
  return (prog, opts, files, errs)
