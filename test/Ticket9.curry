module Ticket9 where

type Options = { optHelp :: Bool }

options :: [Options -> Options]
options = []

parseOpts :: Options
parseOpts = foldl (flip ($)) { optHelp = False } opts
  where opts = options
