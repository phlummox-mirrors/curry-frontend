------------------------------------------------------------------------------
--- Compiler options for the ID-based curry compiler
---
--- @author Fabian Reck, Bjoern Peemoeller
--- @version June 2011
------------------------------------------------------------------------------
module CompilerOpts ( Options (..), defaultOptions) where

type Options = { optHelp :: Bool }

defaultOptions :: Options
defaultOptions = { optHelp = False }

options :: [Options -> Options]
options = []

parseOpts :: Options
parseOpts = foldl (flip ($)) defaultOptions opts
  where opts = options
