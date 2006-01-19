-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- CompilerResult - Provides a record for dealing with compiler results.
--                
-- January 2006,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module CompilerResults where


-------------------------------------------------------------------------------

--
data CompilerResults
   = CompilerResults{ unchangedIntf :: Maybe FilePath }

--
defaultResults :: CompilerResults
defaultResults = CompilerResults{ unchangedIntf = Nothing }


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------