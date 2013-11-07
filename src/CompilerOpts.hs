{- |
    Module      :  $Header$
    Description :  Compiler options
    Copyright   :  (c) 2005        Martin Engelke
                       2007        Sebastian Fischer
                       2011 - 2013 Björn Peemöller
                       2013        Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines data structures holding options for the
    compilation of Curry programs, and utility functions for printing
    help information as well as parsing the command line arguments.
-}
module CompilerOpts
  ( Options (..), CymakeMode (..), Verbosity (..), TargetType (..)
  , WarnFlag (..), Extension (..), DumpLevel (..)
  , dumpLevel, defaultOptions, getCompilerOpts, usage
  ) where

import Data.List             (intercalate, nub)
import System.Console.GetOpt
import System.Environment    (getArgs, getProgName)
import System.FilePath       (splitSearchPath)

import Curry.Files.Filenames (currySubdir)

-- -----------------------------------------------------------------------------
-- Option data structures
-- -----------------------------------------------------------------------------

-- |Data type for recording compiler options
data Options = Options
  -- general
  { optMode         :: CymakeMode   -- ^ modus operandi
  , optVerbosity    :: Verbosity    -- ^ verbosity level
  -- compilation
  , optForce        :: Bool         -- ^ force (re-)compilation of target
  , optLibraryPaths :: [FilePath]   -- ^ directories to search in for libraries
  , optImportPaths  :: [FilePath]   -- ^ directories to search in for imports
  , optUseSubdir    :: Bool         -- ^ use subdir for output?
  , optInterface    :: Bool         -- ^ create a FlatCurry interface file?
  , optWarn         :: Bool         -- ^ show warnings? (legacy option)
  , optWarnFlags    :: [WarnFlag]   -- ^ Warnings flags (see below)
  , optWarnAsError  :: Bool         -- ^ Should warnings be treated as errors?
  , optTargetTypes  :: [TargetType] -- ^ what to generate
  , optExtensions   :: [Extension]  -- ^ enabled language extensions
  , optDumps        :: [DumpLevel]  -- ^ dump levels
  , optDumpEnv      :: Bool         -- ^ dump compilation environment
  , optDumpRaw      :: Bool         -- ^ dump data structure
  , optDumpCompleteEnv :: Bool      -- ^ show complete environment
  } deriving Show

-- | Default compiler options
defaultOptions :: Options
defaultOptions = Options
  { optMode         = ModeMake
  , optVerbosity    = VerbStatus
  , optForce        = False
  , optLibraryPaths = []
  , optImportPaths  = []
  , optUseSubdir    = True
  , optInterface    = True
  , optWarn         = True
  , optWarnFlags    = stdWarnFlags
  , optWarnAsError  = False
  , optTargetTypes  = []
  , optExtensions   = []
  , optDumps        = []
  , optDumpEnv      = False
  , optDumpRaw      = False
  , optDumpCompleteEnv  = False
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
  | VerbInfo   -- ^ also show additional info
  deriving (Eq, Ord, Show)

-- |Description and flag of verbosities
verbosities :: [(Verbosity, String, String)]
verbosities = [ ( VerbQuiet , "0", "quiet" )
              , ( VerbStatus, "1", "status")
              , ( VerbInfo  , "2", "info"  )
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
  [ (WarnMultipleImports   , "multiple-imports"   , "multiple imports"           )
  , (WarnDisjoinedRules    , "disjoined-rules"    , "disjoined function rules"   )
  , (WarnUnusedBindings    , "unused-bindings"    , "unused bindings"            )
  , (WarnNameShadowing     , "name-shadowing"     , "name shadowing"             )
  , (WarnOverlapping       , "overlapping"        , "overlapping function rules" )
  , (WarnIncompletePatterns, "incomplete-patterns", "incomplete pattern matching")
  , (WarnIdleAlternatives  , "idle-alternatives"  , "idle case alternatives"     )
  ]

-- |Dump level
data DumpLevel
  = DumpParsed             -- ^ dump source code after parsing
  | DumpTypeClassesChecked -- ^ dump source code after type class checking
  | DumpKindChecked        -- ^ dump source code after kind checking
  | DumpSyntaxChecked      -- ^ dump source code after syntax checking
  | DumpPrecChecked        -- ^ dump source code after precedence checking
  | DumpTypeChecked        -- ^ dump source code after type checking
  | DumpDictionaries       -- ^ dump source code after dictionaries have been inserted
  | DumpTypeChecked2       -- ^ dump source code after second type checking
  | DumpExportChecked      -- ^ dump source code after export checking
  | DumpQualified          -- ^ dump source  after qualification
  | DumpDesugared          -- ^ dump source  after desugaring
  | DumpSimplified         -- ^ dump source  after simplification
  | DumpLifted             -- ^ dump source  after lambda-lifting
  | DumpTranslated         -- ^ dump IL code after translation
  | DumpCaseCompleted      -- ^ dump IL code after case completion
    deriving (Eq, Bounded, Enum, Show)

-- |Description and flag of dump levels
dumpLevel :: [(DumpLevel, String, String)]
dumpLevel = [ (DumpParsed       , "dump-parse", "parse tree"               )
            , (DumpKindChecked  , "dump-kc"   , "kind checker output"      )
            , (DumpSyntaxChecked, "dump-sc"   , "syntax checker output"    )
            , (DumpPrecChecked  , "dump-pc"   , "precedence checker output")
            , (DumpTypeClassesChecked, "dump-tcc", "type classes checker output")
            , (DumpTypeChecked  , "dump-tc"   , "type checker output"      )
            , (DumpDictionaries , "dump-dict" , "dictionaries inserter output")
            , (DumpTypeChecked2 , "dump-tc2"  , "second type checker output")
            , (DumpExportChecked, "dump-ec"   , "export checker output"    )
            , (DumpQualified    , "dump-qual" , "qualifier output"         )
            , (DumpDesugared    , "dump-ds"   , "desugarer output"         )
            , (DumpSimplified   , "dump-simpl", "simplifier output"        )
            , (DumpLifted       , "dump-lift" , "lifting output"           )
            , (DumpTranslated   , "dump-trans", "translated output"        )
            , (DumpCaseCompleted, "dump-cc"   , "case completed output"    )
            ]

-- |Language extensions
data Extension
  = Records
  | FunctionalPatterns
  | AnonFreeVars
  | NoImplicitPrelude
  | TypeClassExtensions
    deriving (Eq, Read, Show)

-- |Description and flag of language extensions
extensions :: [(Extension, String, String)]
extensions =
  [ ( Records           , "Records"
    , "enable record syntax"                )
  , ( FunctionalPatterns, "FunctionalPatterns"
    , "enable functional patterns"          )
  , ( AnonFreeVars      , "AnonFreeVars"
    , "enable anonymous free variables"     )
  , ( NoImplicitPrelude , "NoImplicitPrelude"
    , "do not implicitly import the Prelude")
  , ( TypeClassExtensions, "TypeClassExtensions"
    , "enable type classes"                 )
  ]

-- |Language 'Extension's enabled by @-e@ flag
curryExtensions :: [Extension]
curryExtensions = [Records, FunctionalPatterns, AnonFreeVars]

-- -----------------------------------------------------------------------------
-- Parsing of the command line options.
--
-- Because some flags require additional arguments, the structure is slightly
-- more complicated to enable malformed arguments to be reported.
-- -----------------------------------------------------------------------------

type OptErr = (Options, [String])

type OptErrTable = [(String, String, Options -> Options)]

onOpts :: (Options -> Options) -> OptErr -> OptErr
onOpts f (opts, errs) = (f opts, errs)

onOptsArg :: (String -> Options -> Options) -> String -> OptErr -> OptErr
onOptsArg f arg (opts, errs) = (f arg opts, errs)

addErr :: String -> OptErr -> OptErr
addErr err (opts, errs) = (opts, errs ++ [err])

mkOptErrOption :: String -> [String] -> String -> String -> OptErrTable
               -> OptDescr (OptErr -> OptErr)
mkOptErrOption flags longFlags arg what tbl = Option flags longFlags
  (ReqArg (parseOptErr what tbl) arg)
  ("set " ++ what ++ " `" ++ arg ++ "', where `" ++ arg ++ "' is one of\n"
    ++ renderOptErrTable tbl)

parseOptErr :: String -> OptErrTable -> String -> OptErr -> OptErr
parseOptErr what table opt = case lookup3 opt table of
  Just f  -> onOpts f
  Nothing -> addErr $ "unrecognized " ++ what ++ '`' : opt ++ "'\n"
  where
  lookup3 _ []                  = Nothing
  lookup3 k ((k', _, v2) : kvs)
    | k == k'                   = Just v2
    | otherwise                 = lookup3 k kvs

renderOptErrTable :: OptErrTable -> String
renderOptErrTable ds
  = intercalate "\n" $ map (\(k, d, _) -> rpad maxLen k ++ ": " ++ d) ds
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
  , Option ""   ["html"]
      (NoArg (onOpts $ \ opts -> opts { optMode = ModeHtml }))
      "generate html code and exit"
  -- verbosity
  , mkOptErrOption "v" ["verbosity"] "n" "verbosity level" verbDescriptions
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
  , Option ""   ["no-subdir"]
      (NoArg (onOpts $ \ opts -> opts { optUseSubdir = False }))
      ("disable writing to `" ++ currySubdir ++ "' subdirectory")
  , Option ""   ["no-intf"]
      (NoArg (onOpts $ \ opts -> opts { optInterface = False }))
      "do not create an interface file"
    -- legacy warning flags
  , Option ""   ["no-warn"]
      (NoArg (onOpts $ \ opts -> opts { optWarn = False }))
      "do not print warnings"
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
  , mkOptErrOption "X" [] "ext" "language extension" extDescriptions
  , mkOptErrOption "W" [] "opt" "warning option"     warnDescriptions
  , mkOptErrOption "d" [] "opt" "debug option"       debugDescriptions
  ]

verbDescriptions :: OptErrTable
verbDescriptions = map toDescr verbosities
  where
  toDescr (flag, name, desc)
    = (name, desc, \ opts -> opts { optVerbosity = flag })

extDescriptions :: OptErrTable
extDescriptions = map toDescr extensions
  where
  toDescr (flag, name, desc)
    = (name, desc,
        \ opts -> opts { optExtensions = addFlag flag (optExtensions opts)})

warnDescriptions :: OptErrTable
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

debugDescriptions :: OptErrTable
debugDescriptions =
  [ ( "dump-all", "dump everything"
    , \ opts -> opts { optDumps = [minBound .. maxBound] })
  , ( "dump-none", "dump nothing"
    , \ opts -> opts { optDumps = []                     })
  , ( "dump-env" , "additionally dump compiler environment"
    , \ opts -> opts { optDumpEnv = True                 })
  , ( "dump-raw" , "dump as raw AST (instead of pretty printed)"
    , \ opts -> opts { optDumpRaw = True                 })
  , ( "dump-complete-env", "dump the complete environment"
    , \ opts -> opts { optDumpCompleteEnv = True         })
  ] ++ map toDescr dumpLevel
  where
  toDescr (flag, name, desc)
    = (name , "dump " ++ desc
        , \ opts -> opts { optDumps = addFlag flag (optDumps opts)})

addFlag :: Eq a => a -> [a] -> [a]
addFlag o opts = nub $ o : opts

removeFlag :: Eq a => a -> [a] -> [a]
removeFlag o opts = filter (/= o) opts

-- |Parse the command line arguments
parseOpts :: [String] -> (Options, [String], [String])
parseOpts args = (opts, files, errs ++ errs2)
  where
  (opts, errs2) = foldl (flip ($)) (defaultOptions, []) optErrs
  (optErrs, files, errs) = getOpt Permute options args

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
