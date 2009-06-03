-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- CurryBuilderOpts - Defines data structures containing options for
--                    building Curry representations (see module
--                    "CurryBuilder")
--
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
-- March 2007, extensions by Sebastian Fischer (sebf@informatik.uni-kiel.de)
--
module CurryBuilderOpts where

import GetOpt
import CurryCompilerOpts (Dump(..))
--import Options (Dump(..))


-------------------------------------------------------------------------------

-- Data type for recording builder options
data Options 
   = Options{ force :: Bool,              -- force compilation
              html :: Bool,               -- generate Html code  
	      importPaths :: [FilePath],  -- import paths
	      libPaths :: [FilePath],     -- library paths
	      output :: Maybe FilePath,   -- output file paths
	      noVerb :: Bool,             -- verbosity on/off
	      noWarn :: Bool,             -- warnings on/off
	      noOverlapWarn :: Bool,      -- "overlap" warnings on/off
	      flat :: Bool,               -- generate FlatCurry code
              flatWithSrcRefs :: Bool,    -- generate code with src references
	      flatXml :: Bool,            -- generate FlatXML code
	      abstract :: Bool,           -- generate AbstractCurry code
	      untypedAbstract :: Bool,    -- generate untyped AbstractCurry
	      parseOnly :: Bool,          -- generate source representation
	      withExtensions :: Bool,     -- enable extended functionalities
	      dump :: [Dump]              -- dumps
	    }

-- Default builder options
defaultOpts = Options{ force           = False,
                       html            = False,
		       importPaths     = [],
		       libPaths        = [],
		       output          = Nothing,
		       noVerb          = False,
		       noWarn          = False,
		       noOverlapWarn   = False,
		       flat            = False,
                       flatWithSrcRefs = False,
		       flatXml         = False,
		       abstract        = False,
		       untypedAbstract = False,
		       parseOnly       = False,
		       withExtensions  = False,
		       dump            = []
		     }


-- Data type for representing all available options (needed to read and parse
-- the options from the command line; see module "GetOpt")
data Option = Help | Force | Html
	    | ImportPath FilePath | LibPath FilePath | Output FilePath
	    | NoVerb | NoWarn | NoOverlapWarn
	    | Flat | FlatXML | Abstract | UntypedAbstract | ParseOnly
            | FlatWithSrcRefs
	    | WithExtensions
	    | Dump [Dump]
	    deriving Eq


-- All available builder options
options = [Option "f" ["force"] (NoArg Force)
	          "force compilation of dependent files",
          Option "" ["html"] (NoArg Html)
                 "generate html code",
	   Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
	          "search for imported modules in DIR",
	   Option "o" ["output"] (ReqArg Output "FILE")
	          "output goes to FILE",
	   Option "P" ["lib-dir"] (ReqArg LibPath "DIR")
	          "search for library interfaces in DIR",
	   Option "" ["no-verb"] (NoArg NoVerb)
	          "do not print compiler messages",
	   Option "" ["no-warn"] (NoArg NoWarn)
	          "do not print any warning",
	   Option "" ["no-overlap-warn"] (NoArg NoOverlapWarn)
	          "do not print warnings for overlapping rules",
	   Option ""  ["flat"] (NoArg Flat)
	          "generate FlatCurry code",
	   Option ""  ["xml"] (NoArg FlatXML)
	          "generate flat xml code",
           Option "" ["no-simp"] (NoArg FlatWithSrcRefs)
                  "do not simplify code before lambda lifting",
	   Option ""  ["acy"] (NoArg Abstract)
	          "generate (type infered) AbstractCurry code",
	   Option ""  ["uacy"] (NoArg UntypedAbstract)
	          "generate untyped AbstractCurry code",
	   Option ""  ["parse-only"] (NoArg ParseOnly)
	          "generate source representation",
	   Option "e"  ["extended"] (NoArg WithExtensions)
	          "enable extended Curry functionalities",
	   Option ""  ["dump-all"] (NoArg (Dump [minBound..maxBound]))
                  "dump everything",
	   Option "?h" ["help"] (NoArg Help)
	          "display this help and exit"
           
	  ]


-- Inserts an option (type 'Option') into the options record (type 'Options')
selectOption :: Option -> Options -> Options
selectOption Force opts           = opts{ force = True }
selectOption (ImportPath dir) opts 
   = opts{ importPaths = dir:(importPaths opts) }
selectOption (LibPath dir) opts 
   = opts{ libPaths = dir:(libPaths opts) }
selectOption (Output file) opts   = opts{ output = Just file }
selectOption NoVerb opts          = opts{ noVerb = True, 
					  noWarn = True,
					  noOverlapWarn = True }
selectOption NoWarn opts          = opts{ noWarn = True }
selectOption NoOverlapWarn opts   = opts{ noOverlapWarn = True }
selectOption Flat opts            = opts{ flat = True }
selectOption FlatWithSrcRefs opts = opts{ flatWithSrcRefs = True }
selectOption Html opts            = opts{ html = True }
selectOption FlatXML opts         = opts{ flatXml = True }
selectOption Abstract opts        = opts{ abstract = True }
selectOption UntypedAbstract opts = opts{ untypedAbstract = True }
selectOption ParseOnly opts       = opts{ parseOnly = True }
selectOption WithExtensions opts  = opts{ withExtensions = True }
selectOption (Dump ds) opts       = opts{ dump = ds ++ dump opts }


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
