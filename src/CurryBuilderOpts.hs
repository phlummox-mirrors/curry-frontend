-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- CurryBuilderOpts - Defines data structures containing options for
--                    building Curry representations (see module
--                    "CurryBuilder")
--
-- September 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module CurryBuilderOpts where

import GetOpt


-------------------------------------------------------------------------------

-- Data type for recording builder options
data Options 
   = Options{importPaths :: [FilePath],  -- import paths
	     libPaths :: [FilePath],     -- library paths
	     output :: Maybe FilePath,   -- output file paths
	     flat :: Bool,               -- generate FlatCurry code
	     flatXml :: Bool,            -- generate FlatXML code
	     abstract :: Bool,           -- generate AbstractCurry code
	     untypedAbstract :: Bool     -- generate untyped AbstractCurry
	    }                             -- code

-- Default builder options
defaultOpts = Options{importPaths     = [],
		      libPaths        = [],
		      output          = Nothing,
		      flat            = False,
		      flatXml         = False,
		      abstract        = False,
		      untypedAbstract = False
		     }


-- Data type for representing all available options (needed to read and parse
-- the options from the command line; see module "GetOpt")
data Option = Help | ImportPath FilePath | LibPath FilePath | Output FilePath
	    | Flat | FlatXML | Abstract | UntypedAbstract
	    deriving Eq


-- All available builder options
options = [Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
	          "search for imported modules in DIR",
	   Option "o" ["output"] (ReqArg Output "FILE")
	          "output goes to FILE",
	   Option "P" ["lib-dir"] (ReqArg LibPath "DIR")
	          "search for library interfaces in DIR",
	   Option ""  ["flat"] (NoArg Flat)
	          "generate FlatCurry code",
	   Option ""  ["xml"] (NoArg FlatXML)
	          "generate flat xml code",
	   Option ""  ["acy"] (NoArg Abstract)
	          "generate (type infered) AbstractCurry code",
	   Option ""  ["uacy"] (NoArg UntypedAbstract)
	          "generate untyped AbstractCurry code",
	   Option "?h" ["help"] (NoArg Help)
	          "display this help and exit"
	  ]


-- Inserts an option (type 'Option') into the options record (type 'Options')
selectOption :: Option -> Options -> Options
selectOption (ImportPath dir) opts 
   = opts{ importPaths = dir:(importPaths opts) }
selectOption (LibPath dir) opts 
   = opts{ libPaths = dir:(libPaths opts) }
selectOption (Output file) opts   = opts{ output = Just file }
selectOption Flat opts            = opts{ flat = True }
selectOption FlatXML opts         = opts{ flatXml = True }
selectOption Abstract opts        = opts{ abstract = True }
selectOption UntypedAbstract opts = opts{ untypedAbstract = True }


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
