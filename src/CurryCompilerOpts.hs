-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- CurryCompilerOpts - Defines data structures containing options for
--                     compiling Curry programs (see module "CurryCompiler")
--
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module CurryCompilerOpts where

import GetOpt
--import Options (Dump(..))


-------------------------------------------------------------------------------

-- Data type for recording compiler options
data Options
   = Options{importPaths :: [FilePath], -- directories for searching imports
	     output :: Maybe FilePath,  -- name of output file
	     noInterface :: Bool,       -- do not create an interface file
	     noVerb :: Bool,            -- verbosity on/off
	     noWarn :: Bool,            -- warnings on/off
	     noOverlapWarn :: Bool,     -- "overlap" warnings on/off
	     flat :: Bool,              -- generate FlatCurry code
	     flatXml :: Bool,           -- generate flat XML code
	     abstract :: Bool,          -- generate typed AbstracCurry code
	     untypedAbstract :: Bool,   -- generate untyped AbstractCurry code
	     withExtensions :: Bool,    -- enable extended functionalities
	     dump :: [Dump]             -- dumps
	    }


-- Default compiler options
defaultOpts = Options{importPaths = [],
		      output          = Nothing,
		      noInterface     = False,
		      noVerb          = False,
		      noWarn          = False,
		      noOverlapWarn   = False,
		      flat            = False,
		      flatXml         = False,
		      abstract        = False,
		      untypedAbstract = False,
		      withExtensions  = False,
		      dump            = []
		     }


-- Data type for representing all available options (needed to read and parse
-- the options from the command line; see module "GetOpt")
data Option = Help | ImportPath FilePath | Output FilePath
	    | NoInterface | NoVerb | NoWarn | NoOverlapWarn
	    | FlatXML | Flat | Abstract | UntypedAbstract
	    | WithExtensions
	    | Dump [Dump]


-- All available compiler options
options = [Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
                  "search for imports in DIR",
	   Option "o" ["output"] (ReqArg Output "FILE")
                  "write code to FILE",
	   Option "" ["no-intf"] (NoArg NoInterface)
                  "do not create an interface file",
	   Option "" ["no-verb"] (NoArg NoVerb)
	          "do not print compiler messages",
	   Option "" ["no-warn"] (NoArg NoWarn)
	          "do not print warnings",
	   Option "" ["no-overlap-warn"] (NoArg NoOverlapWarn)
	          "do not print warnings for overlapping rules",
	   Option "" ["flat"] (NoArg Flat)
                  "generate FlatCurry code",
	   Option "" ["xml"] (NoArg FlatXML)
                  "generate flat xml code",
	   Option "" ["acy"] (NoArg Abstract)
                  "generate (type infered) AbstractCurry code",
	   Option "" ["uacy"] (NoArg UntypedAbstract)
                  "generate untyped AbstractCurry code",
	   Option ""  ["extended"] (NoArg WithExtensions)
	          "enable extended Curry functionalities",
	   Option "" ["dump-all"] (NoArg (Dump [minBound..maxBound]))
                  "dump everything",
	   Option "" ["dump-renamed"] (NoArg (Dump [DumpRenamed]))
                  "dump source code after renaming",
	   Option "" ["dump-types"] (NoArg (Dump [DumpTypes]))
                  "dump types after type-checking",
	   Option "" ["dump-desugared"] (NoArg (Dump [DumpDesugared]))
                  "dump source code after desugaring",
	   Option "" ["dump-simplified"] (NoArg (Dump [DumpSimplified]))
                  "dump source code after simplification",
	   Option "" ["dump-lifted"] (NoArg (Dump [DumpLifted]))
                  "dump source code after lambda-lifting",
	   Option "" ["dump-il"] (NoArg (Dump [DumpIL]))
                  "dump intermediate language before lifting",
	   Option "" ["dump-transformed"] (NoArg (Dump [DumpTransformed]))
                  "dump IL code after debugging transformation",
	   Option "" ["dump-normalized"] (NoArg (Dump [DumpNormalized]))
                  "dump IL code after normalization",
	   Option "?h" ["help"] (NoArg Help)
                  "display this help and exit"
	  ]


-- Inserts an option (type 'Option') into the options record (type 'Options')
selectOption :: Option -> Options -> Options
selectOption (ImportPath dir) opts 
   = opts{ importPaths = dir:(importPaths opts) }
selectOption (Output file) opts   = opts{ output = Just file }
selectOption NoInterface opts     = opts{ noInterface = True }
selectOption NoVerb opts          = opts{ noVerb = True, 
					  noWarn = True,
					  noOverlapWarn = True }
selectOption NoWarn opts          = opts{ noWarn = True }
selectOption NoOverlapWarn opts   = opts{ noOverlapWarn = True }
selectOption Flat opts            = opts{ flat = True }
selectOption FlatXML opts         = opts{ flatXml = True }
selectOption Abstract opts        = opts{ abstract = True }
selectOption UntypedAbstract opts = opts{ untypedAbstract = True }
selectOption WithExtensions opts  = opts{ withExtensions = True }
selectOption (Dump ds) opts       = opts{ dump = ds ++ dump opts }


-------------------------------------------------------------------------------

-- Data type for representing code dumps
-- TODO: dump FlatCurry code, dump AbstractCurry code, dump after 'case'
--       expansion
data Dump = DumpRenamed      -- dump source after renaming
	  | DumpTypes        -- dump types after typechecking
	  | DumpDesugared    -- dump source after desugaring
	  | DumpSimplified   -- dump source after simplification
	  | DumpLifted       -- dump source after lambda-lifting
	  | DumpIL           -- dump IL code after translation
	  | DumpTransformed  -- dump transformed code
	  | DumpNormalized   -- dump IL code after normalization
	    deriving (Eq,Bounded,Enum,Show)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------